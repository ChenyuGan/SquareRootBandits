/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCoordinatorUpDecoderReplay
public import Bandits.Support.ReferenceActiveAffinePositiveTest

/-!
# Actual row-local UP call inputs on physical coordinator records

Sources: `sources/zip4/manuscript/05_binary_transport.tex:36-48,70-124`,
`sources/zip4/manuscript/06_interruptions.tex:277-284,327-348`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:92-109`.

This module projects the actual post-choice collection prefix, including its
recording and start-round checks, from a physical step input. It identifies
the retained UP diagnostic with that real row-local receiver call. The
diagnostic is kept distinct from receiver eligibility and positive observation.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.CoordinatorUpReception
open Bandits.Support.CoordinatorCollectionLedger

namespace Bandits.Support.ReferenceCoordinatorUpPhysicalCall

local instance propDecidable (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput

variable {p : Parameters} {rate : RateInput p}

/-- Run the actual collection recorder and stage-(1) start operation from one
post-choice prefix. A failed recorder or checked start contributes no ledger. -/
def tailLedger? {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ) :
    Option (ReferenceActivePhysicalStep.Ledger rate) :=
  match CoordinatorRecorderComplementBridge.run
      (ReferenceActivePhysicalStep.collectionRecordingInput prepared payload started weights) with
  | none => none
  | some recording =>
      match CoordinatorCollectionLedger.startRound ledger (x.time.val + 1)
          (ReferenceActivePhysicalStep.collectionEnabled ledger x.time)
          (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) with
      | .success ledgerStarted => some ledgerStarted
      | .invalid => none
      | .rejected _ => none

/-- The literal ledger at an actual receiver call site. The dispatcher must
have selected an arm, and the original live cutoff or continuing collection
branch supplies the call prefix. No output diagnostic is consulted. -/
def siteLedger? {x : ReferenceActivePhysicalStep.RoundInput p rate} :
    Option (ReferenceActivePhysicalStep.Ledger rate) := by
  let prepared := ReferenceActivePhysicalStep.prepare x
  if prepared.coordinator.selection = none then
    exact none
  else
    match prepared.coordinator with
    | .live registers _ _ (.cutoffChosen dispatched _ ledger _ _ _ _ _ _ _) =>
        exact tailLedger? prepared registers.payload
          (ReferenceActivePhysicalStep.sharedLedger ledger) dispatched.startResult
          (ReferenceActivePhysicalStep.liveRegistersAt registers x.time).complementWeights
    | .collection payload ledger clock cutoff (.continuing _ snapshot _ _) =>
        let source := ReferenceActivePhysicalStep.collectionInput x payload ledger clock cutoff
        exact tailLedger? prepared payload ledger snapshot.clockStarted
          (CoordinatorCollectionInteractive.PreObservationInputs.weights source
            snapshot.inputsValid.ledger_valid snapshot.inputsValid.assignment_eq)
    | _ => exact none

/-- The original row, persistent bank, calendar coordinate, and local
coordinator observation determine the actual reception input. -/
def actualUpInput (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate) :=
  ReferenceUpReception.receptionInputAtRow rate x.row
    (ReferenceActivePhysicalStep.upInputs (ReferenceActivePhysicalStep.prepare x) ledger) x.time

private theorem collectionPostChoice_up_retention
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ) :
    (∃ d, (ReferenceActivePhysicalStep.collectionPostChoice
        (ReferenceActivePhysicalStep.prepare x) payload ledger started weights).up = some d) ↔
      ∃ ledgerStarted, tailLedger? (ReferenceActivePhysicalStep.prepare x)
          payload ledger started weights = some ledgerStarted ∧
        CoordinatorUpReception.receptionInputCheck (actualUpInput x ledgerStarted) = true := by
  classical
  let recordingInput := CoordinatorRecorderComplementBridge.run
      (ReferenceActivePhysicalStep.collectionRecordingInput
        (ReferenceActivePhysicalStep.prepare x) payload started weights)
  cases hrecording : recordingInput with
  | none =>
      simp [tailLedger?, ReferenceActivePhysicalStep.collectionPostChoice, hrecording,
        recordingInput, ReferenceActivePhysicalStep.coordinatorFailure]
  | some recording =>
      cases hstart : CoordinatorCollectionLedger.startRound ledger (x.time.val + 1)
          (ReferenceActivePhysicalStep.collectionEnabled ledger x.time)
          (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) with
      | invalid =>
          simp [tailLedger?, ReferenceActivePhysicalStep.collectionPostChoice, hrecording, hstart,
            recordingInput, ReferenceActivePhysicalStep.coordinatorFailure]
      | rejected rejectedLedger =>
          simp [tailLedger?, ReferenceActivePhysicalStep.collectionPostChoice, hrecording, hstart,
            recordingInput, ReferenceActivePhysicalStep.coordinatorFailure]
      | success ledgerStarted =>
          simp only [ReferenceActivePhysicalStep.collectionPostChoice, recordingInput,
            hrecording, hstart]
          rw [ReferenceActiveAffinePositiveTest.collectionFinish_up]
          let inputs := ReferenceActivePhysicalStep.upInputs
            (ReferenceActivePhysicalStep.prepare x) ledgerStarted
          let input := ReferenceUpReception.receptionInputAtRow rate x.row inputs x.time
          have hinput : input = actualUpInput x ledgerStarted := rfl
          have htail : tailLedger? (ReferenceActivePhysicalStep.prepare x)
              payload ledger started weights = some ledgerStarted := by
            simp [tailLedger?, recordingInput, hrecording, hstart]
          by_cases hcheck : CoordinatorUpReception.receptionInputCheck input = true
          · constructor
            · intro _
              exact ⟨ledgerStarted, htail, by simpa [hinput] using hcheck⟩
            · rintro ⟨ledger', hledger', hcheck'⟩
              have hledger : ledger' = ledgerStarted := by
                simpa [tailLedger?, recordingInput, hrecording, hstart] using hledger'.symm
              subst ledger'
              have hcheckInput :
                  CoordinatorUpReception.receptionInputCheck input = true := by
                simpa [hinput] using hcheck'
              simp [ReferenceActivePhysicalStep.receiveUp, inputs, input, hcheckInput]
          · have hfalse : CoordinatorUpReception.receptionInputCheck input = false := by
              cases hvalue : CoordinatorUpReception.receptionInputCheck input with
              | false => rfl
              | true => exact (hcheck hvalue).elim
            constructor
            · rintro ⟨d, hd⟩
              have : False := by
                simp [ReferenceActivePhysicalStep.receiveUp, inputs, input, hfalse] at hd
              exact this.elim
            · rintro ⟨ledger', hledger', hcheck'⟩
              have hledger : ledger' = ledgerStarted := by
                simpa [tailLedger?, recordingInput, hrecording, hstart] using hledger'.symm
              subst ledger'
              exact (hcheck hcheck').elim

private theorem collectionPostChoice_up_input
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ)
    (d : ReferenceActivePhysicalStep.UpDiagnostic p rate)
    (hd : (ReferenceActivePhysicalStep.collectionPostChoice
        (ReferenceActivePhysicalStep.prepare x) payload ledger started weights).up = some d) :
    ∃ ledgerStarted, tailLedger? (ReferenceActivePhysicalStep.prepare x)
        payload ledger started weights = some ledgerStarted ∧
      CoordinatorUpReception.receptionInputCheck (actualUpInput x ledgerStarted) = true ∧
      d.input = actualUpInput x ledgerStarted ∧
      d.decoderAfter = (CoordinatorUpReception.decoderTransition
        (actualUpInput x ledgerStarted)).1 := by
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
          have hinput : input = actualUpInput x ledgerStarted := rfl
          have hcheck : CoordinatorUpReception.receptionInputCheck input = true := by
            by_contra hnot
            have hfalse : CoordinatorUpReception.receptionInputCheck input = false := by
              cases hval : CoordinatorUpReception.receptionInputCheck input with
              | false => rfl
              | true => exact (hnot hval).elim
            simp [ReferenceActivePhysicalStep.receiveUp, inputs, input, hfalse] at hd
          have hdiagInput :
              (ReferenceActivePhysicalStep.receiveUp
                (ReferenceActivePhysicalStep.prepare x) ledgerStarted).diagnostic.map
                  ReferenceActivePhysicalStep.UpDiagnostic.input = some input := by
            simp [ReferenceActivePhysicalStep.receiveUp, inputs, input, hcheck]
          have hdiagAfter :
              (ReferenceActivePhysicalStep.receiveUp
                (ReferenceActivePhysicalStep.prepare x) ledgerStarted).diagnostic.map
                  ReferenceActivePhysicalStep.UpDiagnostic.decoderAfter =
                    some (CoordinatorUpReception.decoderTransition input).1 := by
            simp [ReferenceActivePhysicalStep.receiveUp, inputs, input, hcheck]
          have hsome := (Option.map_eq_some_iff.mp hdiagInput)
          rcases hsome with ⟨diagnostic, hdiagnostic, hsameInput⟩
          rw [hd] at hdiagnostic
          cases hdiagnostic
          have hsameAfter := (Option.map_eq_some_iff.mp hdiagAfter)
          rcases hsameAfter with ⟨diagnostic', hdiagnostic', hafter⟩
          rw [hd] at hdiagnostic'
          cases hdiagnostic'
          refine ⟨ledgerStarted, ?_, hcheck, ?_, ?_⟩
          · simp [tailLedger?, recordingInput, hrecording, hstart]
          · simpa [input, hinput] using hsameInput
          · simpa [input, hinput] using hafter

private theorem physical_up_retention
    (x : ReferenceActivePhysicalStep.RoundInput p rate) :
    (∃ d, (ReferenceActivePhysicalStep.prepare x).observeCoordinator.up = some d) ↔
      ∃ ledger, siteLedger? (x := x) = some ledger ∧
        CoordinatorUpReception.receptionInputCheck (actualUpInput x ledger) = true := by
  classical
  cases hcoord : (ReferenceActivePhysicalStep.prepare x).coordinator with
  | first outcome =>
      cases outcome with
      | choiceDomainFailure installation =>
          simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
            hcoord, siteLedger?, ReferenceActivePhysicalStep.coordinatorFailure]
      | recorderBoundaryFailure installation =>
          simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
            hcoord, siteLedger?, ReferenceActivePhysicalStep.coordinatorFailure]
      | choiceRejected installation =>
          simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
            hcoord, siteLedger?, ReferenceActivePhysicalStep.coordinatorFailure]
      | chosen installation selected =>
          by_cases hsel :
              ReferenceActivePhysicalStep.DispatchCut.selection
                (.first (.chosen installation selected)) = none
          · simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
              hcoord, hsel, siteLedger?, ReferenceActivePhysicalStep.coordinatorFailure]
          · have hnone : (ReferenceActivePhysicalStep.prepare x).observeCoordinator.up = none := by
              have heq := ReferenceActivePhysicalStep.observeCoordinator_first_equation
                (ReferenceActivePhysicalStep.prepare x)
                (.chosen installation selected) hcoord
              rw [heq, ite_eq_right hsel]
              dsimp
              unfold ReferenceActivePhysicalStep.livePostChoice
              repeat' (first | split | simp [ReferenceActivePhysicalStep.coordinatorFailure])
            simp [hnone, siteLedger?, hcoord]
  | live registers owned base outcome =>
      cases outcome with
      | clockFailure failure _ =>
          simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
            hcoord, siteLedger?, ReferenceActivePhysicalStep.coordinatorFailure]
      | initializerFailure dispatched _ _ _ =>
          simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
            hcoord, siteLedger?, ReferenceActivePhysicalStep.coordinatorFailure]
      | localFailure dispatched _ reason =>
          simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
            hcoord, siteLedger?, ReferenceActivePhysicalStep.coordinatorFailure]
      | cutoffChosen dispatched hstart ledger hinit hledger hdomain hclock hpending
          hnoassignment selection =>
          by_cases hsel :
              ReferenceActivePhysicalStep.DispatchCut.selection
                (.live registers owned base
                  (.cutoffChosen dispatched hstart ledger hinit hledger hdomain hclock
                    hpending hnoassignment selection)) = none
          · simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
              hcoord, hsel, siteLedger?, ReferenceActivePhysicalStep.coordinatorFailure]
          · simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
              hcoord, hsel]
            simpa [siteLedger?, hcoord, hsel] using
              (collectionPostChoice_up_retention x registers.payload
                (ReferenceActivePhysicalStep.sharedLedger ledger) dispatched.startResult
                (ReferenceActivePhysicalStep.liveRegistersAt registers x.time).complementWeights)
      | continuingChosen dispatched startRoundEq continuation selected =>
          by_cases hsel :
              ReferenceActivePhysicalStep.DispatchCut.selection
                (.live registers owned base
                  (.continuingChosen dispatched startRoundEq continuation selected)) = none
          · simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
              hcoord, hsel, siteLedger?, ReferenceActivePhysicalStep.coordinatorFailure]
          · have hnone : (ReferenceActivePhysicalStep.prepare x).observeCoordinator.up = none := by
              have heq := ReferenceActivePhysicalStep.observeCoordinator_live_equation
                (ReferenceActivePhysicalStep.prepare x)
                registers owned base (.continuingChosen dispatched startRoundEq continuation selected) hcoord
              rw [heq, ite_eq_right hsel]
              dsimp
              unfold ReferenceActivePhysicalStep.livePostChoice
              repeat' (first | split | simp [ReferenceActivePhysicalStep.coordinatorFailure])
            simp [hnone, siteLedger?, hcoord]
  | collection payload ledger clock cutoff outcome =>
      cases outcome with
      | clockFailure failure _ =>
          simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
            hcoord, siteLedger?, ReferenceActivePhysicalStep.coordinatorFailure]
      | localFailure started _ _ =>
          simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
            hcoord, siteLedger?, ReferenceActivePhysicalStep.coordinatorFailure]
      | coreFailure core started _ _ =>
          simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
            hcoord, siteLedger?, ReferenceActivePhysicalStep.coordinatorFailure]
      | continuing core snapshot boundary scores =>
          by_cases hsel :
              ReferenceActivePhysicalStep.DispatchCut.selection
                (.collection payload ledger clock cutoff
                  (.continuing core snapshot boundary scores)) = none
          · simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
              hcoord, hsel, siteLedger?, ReferenceActivePhysicalStep.coordinatorFailure]
          · simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
              hcoord, hsel]
            let source := ReferenceActivePhysicalStep.collectionInput x payload ledger clock cutoff
            simpa [siteLedger?, hcoord, hsel] using
              (collectionPostChoice_up_retention x payload ledger snapshot.clockStarted
                (CoordinatorCollectionInteractive.PreObservationInputs.weights source
                  snapshot.inputsValid.ledger_valid snapshot.inputsValid.assignment_eq))
      | laterReconstructionFailure core consistent started _ instruction _ _ =>
          simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
            hcoord, siteLedger?,
            ReferenceActivePhysicalStep.coordinatorFailure]
      | laterPrefixFailure core consistent started _ instruction _ _ _ =>
          simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
            hcoord, siteLedger?,
            ReferenceActivePhysicalStep.coordinatorFailure]
      | laterOrientationFailure core consistent started _ instruction _ _ =>
          simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
            hcoord, siteLedger?,
            ReferenceActivePhysicalStep.coordinatorFailure]
      | laterChoiceFailure core consistent started startRoundEq instruction assignmentStartEq
          output localEq clockData installed reason =>
          simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
            hcoord, siteLedger?,
            ReferenceActivePhysicalStep.coordinatorFailure]
      | laterChosen core consistent started startRoundEq instruction assignmentStartEq output
          localEq clockData installed selected =>
          by_cases hsel :
              ReferenceActivePhysicalStep.DispatchCut.selection
                (.collection payload ledger clock cutoff
                  (.laterChosen core consistent started startRoundEq instruction assignmentStartEq
                    output localEq clockData installed selected)) = none
          · simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
              hcoord, hsel, siteLedger?, ReferenceActivePhysicalStep.coordinatorFailure]
          · have hnone : (ReferenceActivePhysicalStep.prepare x).observeCoordinator.up = none := by
              have heq := ReferenceActivePhysicalStep.observeCoordinator_collection_equation
                (ReferenceActivePhysicalStep.prepare x)
                payload ledger clock cutoff
                (.laterChosen core consistent started startRoundEq instruction assignmentStartEq
                  output localEq clockData installed selected) hcoord
              rw [heq, ite_eq_right hsel]
              dsimp
              unfold ReferenceActivePhysicalStep.livePostChoice
              repeat' (first | split | simp [ReferenceActivePhysicalStep.coordinatorFailure])
            simp [hnone, siteLedger?, hcoord]
  | invalidCollectionCutoff =>
      simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
        hcoord, siteLedger?, ReferenceActivePhysicalStep.DispatchCut.selection,
        ReferenceActivePhysicalStep.coordinatorFailure]
  | dagger =>
      simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
        hcoord, siteLedger?, ReferenceActivePhysicalStep.DispatchCut.selection]

/-- Every retained coordinator UP diagnostic is exactly a reached,
domain-checked physical receiver call. No sender, endpoint, success, or
ordinary-state premise is required. -/
theorem record_up_retention_iff
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) :
    (∃ d, r.output.coordinator.up = some d) ↔
      ∃ ledger, siteLedger? (x := r.input) = some ledger ∧
        CoordinatorUpReception.receptionInputCheck (actualUpInput r.input ledger) = true := by
  have hstep : r.output.coordinator.up =
      (ReferenceActivePhysicalStep.prepare r.input).observeCoordinator.up := by
    rw [r.output_eq]
    rfl
  rw [hstep]
  exact physical_up_retention r.input

/-- The actual checked-reception result saved in a physical UP diagnostic. -/
theorem record_retained_up_input
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (d : ReferenceActivePhysicalStep.UpDiagnostic p rate)
    (hd : r.output.coordinator.up = some d) :
    ∃ ledger, siteLedger? (x := r.input) = some ledger ∧
      CoordinatorUpReception.receptionInputCheck (actualUpInput r.input ledger) = true ∧
      d.input = actualUpInput r.input ledger ∧
      d.decoderAfter = (CoordinatorUpReception.decoderTransition
        (actualUpInput r.input ledger)).1 := by
  have hstep : r.output.coordinator.up =
      (ReferenceActivePhysicalStep.prepare r.input).observeCoordinator.up := by
    rw [r.output_eq]
    rfl
  rw [hstep] at hd
  classical
  let x := r.input
  cases hcoord : (ReferenceActivePhysicalStep.prepare x).coordinator with
  | first outcome =>
      cases outcome with
      | choiceDomainFailure installation =>
          simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
            x, hcoord, ReferenceActivePhysicalStep.coordinatorFailure] at hd
      | recorderBoundaryFailure installation =>
          simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
            x, hcoord, ReferenceActivePhysicalStep.coordinatorFailure] at hd
      | choiceRejected installation =>
          simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
            x, hcoord, ReferenceActivePhysicalStep.coordinatorFailure] at hd
      | chosen installation selected =>
          by_cases hsel :
              ReferenceActivePhysicalStep.DispatchCut.selection
                (.first (.chosen installation selected)) = none
          · simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
              x, hcoord, hsel, ReferenceActivePhysicalStep.coordinatorFailure] at hd
          · have hnone : (ReferenceActivePhysicalStep.prepare x).observeCoordinator.up = none := by
              have heq := ReferenceActivePhysicalStep.observeCoordinator_first_equation
                (ReferenceActivePhysicalStep.prepare x)
                (.chosen installation selected) hcoord
              rw [heq, ite_eq_right hsel]
              dsimp
              unfold ReferenceActivePhysicalStep.livePostChoice
              repeat' (first | split | simp [ReferenceActivePhysicalStep.coordinatorFailure])
            rw [hnone] at hd
            cases hd
  | live registers owned base outcome =>
      cases outcome with
      | clockFailure failure _ =>
          simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
            x, hcoord, ReferenceActivePhysicalStep.coordinatorFailure] at hd
      | initializerFailure dispatched _ _ _ =>
          simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
            x, hcoord, ReferenceActivePhysicalStep.coordinatorFailure] at hd
      | localFailure dispatched _ reason =>
          simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
            x, hcoord, ReferenceActivePhysicalStep.coordinatorFailure] at hd
      | cutoffChosen dispatched hstart ledger hinit hledger hdomain hclock hpending hnoassignment selected =>
          by_cases hsel :
              ReferenceActivePhysicalStep.DispatchCut.selection
                (.live registers owned base
                  (.cutoffChosen dispatched hstart ledger hinit hledger hdomain hclock hpending
                    hnoassignment selected)) = none
          · simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
              x, hcoord, hsel, ReferenceActivePhysicalStep.coordinatorFailure] at hd
          · simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
              x, hcoord, hsel] at hd
            obtain ⟨ledgerStarted, hsite, hcheck, hinput, hafter⟩ :=
              collectionPostChoice_up_input x registers.payload
                (ReferenceActivePhysicalStep.sharedLedger ledger) dispatched.startResult
                (ReferenceActivePhysicalStep.liveRegistersAt registers x.time).complementWeights d hd
            refine ⟨ledgerStarted, ?_, hcheck, hinput, hafter⟩
            simpa [siteLedger?, x, hcoord, hsel] using hsite
      | continuingChosen dispatched startRoundEq continuation selected =>
          by_cases hsel :
              ReferenceActivePhysicalStep.DispatchCut.selection
                (.live registers owned base
                  (.continuingChosen dispatched startRoundEq continuation selected)) = none
          · simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
              x, hcoord, hsel, ReferenceActivePhysicalStep.coordinatorFailure] at hd
          · have hnone : (ReferenceActivePhysicalStep.prepare x).observeCoordinator.up = none := by
              have heq := ReferenceActivePhysicalStep.observeCoordinator_live_equation
                (ReferenceActivePhysicalStep.prepare x)
                registers owned base (.continuingChosen dispatched startRoundEq continuation selected) hcoord
              rw [heq, ite_eq_right hsel]
              dsimp
              unfold ReferenceActivePhysicalStep.livePostChoice
              repeat' (first | split | simp [ReferenceActivePhysicalStep.coordinatorFailure])
            rw [hnone] at hd
            cases hd
  | collection payload ledger clock cutoff outcome =>
      cases outcome with
      | clockFailure failure _ =>
          simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
            x, hcoord, ReferenceActivePhysicalStep.coordinatorFailure] at hd
      | localFailure started _ _ =>
          simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
            x, hcoord, ReferenceActivePhysicalStep.coordinatorFailure] at hd
      | coreFailure core started _ _ =>
          simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
            x, hcoord, ReferenceActivePhysicalStep.coordinatorFailure] at hd
      | continuing core snapshot boundary scores =>
          by_cases hsel :
              ReferenceActivePhysicalStep.DispatchCut.selection
                (.collection payload ledger clock cutoff
                  (.continuing core snapshot boundary scores)) = none
          · simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
              x, hcoord, hsel, ReferenceActivePhysicalStep.coordinatorFailure] at hd
          · simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
              x, hcoord, hsel] at hd
            let source := ReferenceActivePhysicalStep.collectionInput x payload ledger clock cutoff
            obtain ⟨ledgerStarted, hsite, hcheck, hinput, hafter⟩ :=
              collectionPostChoice_up_input x payload ledger snapshot.clockStarted
                (CoordinatorCollectionInteractive.PreObservationInputs.weights source
                  snapshot.inputsValid.ledger_valid snapshot.inputsValid.assignment_eq) d hd
            refine ⟨ledgerStarted, ?_, hcheck, hinput, hafter⟩
            simpa [siteLedger?, x, hcoord, hsel, source] using hsite
      | laterReconstructionFailure core consistent started _ instruction _ _ =>
          simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
            x, hcoord,
            ReferenceActivePhysicalStep.coordinatorFailure] at hd
      | laterPrefixFailure core consistent started _ instruction _ _ _ =>
          simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
            x, hcoord,
            ReferenceActivePhysicalStep.coordinatorFailure] at hd
      | laterOrientationFailure core consistent started _ instruction _ _ =>
          simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
            x, hcoord,
            ReferenceActivePhysicalStep.coordinatorFailure] at hd
      | laterChoiceFailure core consistent started startRoundEq instruction assignmentStartEq
          output localEq clockData installed reason =>
          simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
            x, hcoord,
            ReferenceActivePhysicalStep.coordinatorFailure] at hd
      | laterChosen core consistent started startRoundEq instruction assignmentStartEq output
          localEq clockData installed selected =>
          by_cases hsel :
              ReferenceActivePhysicalStep.DispatchCut.selection
                (.collection payload ledger clock cutoff
                  (.laterChosen core consistent started startRoundEq instruction assignmentStartEq
                    output localEq clockData installed selected)) = none
          · simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
              x, hcoord, hsel, ReferenceActivePhysicalStep.coordinatorFailure] at hd
          · have hnone : (ReferenceActivePhysicalStep.prepare x).observeCoordinator.up = none := by
              have heq := ReferenceActivePhysicalStep.observeCoordinator_collection_equation
                (ReferenceActivePhysicalStep.prepare x)
                payload ledger clock cutoff
                (.laterChosen core consistent started startRoundEq instruction assignmentStartEq
                  output localEq clockData installed selected) hcoord
              rw [heq, ite_eq_right hsel]
              dsimp
              unfold ReferenceActivePhysicalStep.livePostChoice
              repeat' (first | split | simp [ReferenceActivePhysicalStep.coordinatorFailure])
            rw [hnone] at hd
            cases hd
  | invalidCollectionCutoff =>
      simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
        x, hcoord, ReferenceActivePhysicalStep.DispatchCut.selection,
        ReferenceActivePhysicalStep.coordinatorFailure] at hd
  | dagger =>
      simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
        x, hcoord, ReferenceActivePhysicalStep.DispatchCut.selection] at hd

/-- All fields of a retained UP call come from the same original row and
prepared physical feedback. The affine coordinate retains the UP direction
and the selected follower inside the original continuous table coordinate. -/
theorem record_retained_up_input_fields
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (d : ReferenceActivePhysicalStep.UpDiagnostic p rate)
    (hd : r.output.coordinator.up = some d) :
    ∃ ledger, siteLedger? (x := r.input) = some ledger ∧
      d.input.ledger = ledger ∧
      d.input.upDecoderBank = r.input.state.upDecoderBank ∧
      d.input.time = r.input.time ∧
      d.input.ownObservation =
        (ReferenceActivePhysicalStep.prepare r.input).feedback.feedback
          (ActiveRoundActions.coordinator p.two_le_m) ∧
      d.input.selectedFollower =
        CoordinatorUpMeasurability.selectedFollowerIndex
          ((r.input.rows r.input.selected).2 r.input.time) ∧
      d.input.affineSample =
        ((r.input.rows r.input.selected).2 r.input.time).2
          (1, CoordinatorUpMeasurability.selectedChannelFollower
            ((r.input.rows r.input.selected).2 r.input.time)) ∧
      d.input.slot = PublicDiscreteDraws.slotDraw
        ((r.input.rows r.input.selected).2 r.input.time).1 ∧
      (CoordinatorUpReception.roundInput d.input).receiverEnabled = true ∧
      (CoordinatorUpReception.roundInput d.input).selected = decide
        (ledger.cutoff ≤ r.input.time.val + 1 ∧
          d.input.slot = PublicDiscreteDraws.upSlot ∧
          d.input.selectedFollower ∈ ledger.pending) ∧
      (CoordinatorUpReception.roundInput d.input).sample = d.input.affineSample ∧
      (CoordinatorUpReception.roundInput d.input).roundedReward =
        CoordinatorUpReception.roundedObservationValue p
          ((ReferenceActivePhysicalStep.prepare r.input).feedback.feedback
            (ActiveRoundActions.coordinator p.two_le_m)) ∧
      (ReferenceActivePhysicalStep.prepare r.input).feedback.feedback
          (ActiveRoundActions.coordinator p.two_le_m) =
        if FiniteBanditModel.collisionFreeFor
            (ReferenceActivePhysicalStep.prepare r.input).arms.actions
              (ActiveRoundActions.coordinator p.two_le_m) then
          r.input.rewards r.input.time
            ((ReferenceActivePhysicalStep.prepare r.input).arms.actions
              (ActiveRoundActions.coordinator p.two_le_m))
        else 0 := by
  classical
  obtain ⟨ledger, hsite, hcheck, hinput, _⟩ := record_retained_up_input r d hd
  have hledger : d.input.ledger = ledger := by
    simpa [actualUpInput, ReferenceActivePhysicalStep.upInputs,
      ReferenceUpReception.receptionInputAtRow,
      CoordinatorUpMeasurability.receptionInputAtRow] using
      congrArg CoordinatorUpReception.ReceptionInput.ledger hinput
  have hbank : d.input.upDecoderBank = r.input.state.upDecoderBank := by
    simpa [actualUpInput, ReferenceActivePhysicalStep.upInputs,
      ReferenceUpReception.receptionInputAtRow,
      CoordinatorUpMeasurability.receptionInputAtRow] using
      congrArg CoordinatorUpReception.ReceptionInput.upDecoderBank hinput
  have htime : d.input.time = r.input.time := by
    simpa [actualUpInput, ReferenceActivePhysicalStep.upInputs,
      ReferenceUpReception.receptionInputAtRow,
      CoordinatorUpMeasurability.receptionInputAtRow] using
      congrArg CoordinatorUpReception.ReceptionInput.time hinput
  have hobs : d.input.ownObservation =
      (ReferenceActivePhysicalStep.prepare r.input).feedback.feedback
        (ActiveRoundActions.coordinator p.two_le_m) := by
    simpa [actualUpInput, ReferenceActivePhysicalStep.upInputs,
      ReferenceActivePhysicalStep.PreparedRound.coordinatorObservation,
      ReferenceUpReception.receptionInputAtRow,
      CoordinatorUpMeasurability.receptionInputAtRow] using
      congrArg CoordinatorUpReception.ReceptionInput.ownObservation hinput
  have hselected : d.input.selectedFollower =
      CoordinatorUpMeasurability.selectedFollowerIndex
        ((r.input.rows r.input.selected).2 r.input.time) := by
    simpa only [actualUpInput, ReferenceActivePhysicalStep.upInputs,
      ReferenceUpReception.receptionInputAtRow_selectedFollower,
      ReferenceActivePhysicalStep.RoundInput.row] using
      congrArg CoordinatorUpReception.ReceptionInput.selectedFollower hinput
  have hsample : d.input.affineSample =
      ((r.input.rows r.input.selected).2 r.input.time).2
        (1, CoordinatorUpMeasurability.selectedChannelFollower
          ((r.input.rows r.input.selected).2 r.input.time)) := by
    simpa only [actualUpInput, ReferenceActivePhysicalStep.upInputs,
      ReferenceUpReception.receptionInputAtRow_affineSample,
      ReferenceActivePhysicalStep.RoundInput.row] using
      congrArg CoordinatorUpReception.ReceptionInput.affineSample hinput
  have hslot : d.input.slot = PublicDiscreteDraws.slotDraw
      ((r.input.rows r.input.selected).2 r.input.time).1 := by
    simpa [actualUpInput, ReferenceActivePhysicalStep.upInputs,
      ReferenceUpReception.receptionInputAtRow,
      CoordinatorUpMeasurability.receptionInputAtRow,
      CoordinatorUpMeasurability.receptionInputAtControl_slot,
      ReferenceActivePhysicalStep.RoundInput.row] using
      congrArg CoordinatorUpReception.ReceptionInput.slot hinput
  have hactualTime : (actualUpInput r.input ledger).time = r.input.time := by
    simp [actualUpInput, ReferenceActivePhysicalStep.upInputs,
      ReferenceUpReception.receptionInputAtRow,
      CoordinatorUpMeasurability.receptionInputAtRow]
  refine ⟨ledger, hsite, hledger, hbank, htime, hobs, hselected, hsample, hslot,
    rfl, ?_, rfl, ?_, ?_⟩
  · have hs : (CoordinatorUpReception.roundInput d.input).selected =
        decide (CoordinatorUpReception.receptionGate d.input) := rfl
    simpa [CoordinatorUpReception.receptionGate, hledger, htime,
      CoordinatorCollectionLedger.sourceRound] using hs
  · rw [hinput]
    simp [CoordinatorUpReception.roundInput, actualUpInput,
      ReferenceActivePhysicalStep.upInputs, ReferenceActivePhysicalStep.PreparedRound.coordinatorObservation,
      ReferenceUpReception.receptionInputAtRow, CoordinatorUpMeasurability.receptionInputAtRow]
  · exact (ReferenceActivePhysicalStep.prepare r.input).feedback_rule
      (ActiveRoundActions.coordinator p.two_le_m)

/-- The physical record's coordinator own-entry projection agrees with the
feedback used in its retained UP input. -/
theorem record_retained_up_own_entry
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) :
    r.output.ownEntries (ActiveRoundActions.coordinator p.two_le_m) =
      ((r.output.preparation.arms.actions
          (ActiveRoundActions.coordinator p.two_le_m)),
        ActualInitializationPhysicalStep.observationOfGrid p
          ((r.output.preparation.feedback.feedback
            (ActiveRoundActions.coordinator p.two_le_m)))) := by
  exact r.ownEntries_formula (ActiveRoundActions.coordinator p.two_le_m)

private theorem tailLedger?_success
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ)
    (ledgerStarted : ReferenceActivePhysicalStep.Ledger rate)
    (htail : tailLedger? prepared payload ledger started weights = some ledgerStarted) :
    ∃ recording : CoordinatorRecordingOperation.Output p,
      CoordinatorRecorderComplementBridge.run
        (ReferenceActivePhysicalStep.collectionRecordingInput prepared payload started weights) =
          some recording ∧
      CoordinatorCollectionLedger.startRound ledger (x.time.val + 1)
        (ReferenceActivePhysicalStep.collectionEnabled ledger x.time)
        (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) =
          .success ledgerStarted := by
  classical
  let recordingInput := CoordinatorRecorderComplementBridge.run
      (ReferenceActivePhysicalStep.collectionRecordingInput prepared payload started weights)
  cases hrecording : recordingInput with
  | none => simp [tailLedger?, recordingInput, hrecording] at htail
  | some recording =>
      cases hstart : CoordinatorCollectionLedger.startRound ledger (x.time.val + 1)
          (ReferenceActivePhysicalStep.collectionEnabled ledger x.time)
          (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) with
      | invalid => simp [tailLedger?, recordingInput, hrecording, hstart] at htail
      | rejected rejectedLedger => simp [tailLedger?, recordingInput, hrecording, hstart] at htail
      | success startedLedger =>
          have heq : startedLedger = ledgerStarted := by
            have hsome : some startedLedger = some ledgerStarted := by
              simpa [tailLedger?, recordingInput, hrecording, hstart] using htail
            exact Option.some.inj hsome
          subst startedLedger
          exact ⟨recording, by simpa [recordingInput] using hrecording, hstart⟩

private theorem sourceCollection_of_preparedCollection
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (clock : CoordinatorPhaseClock.ClockRegisters p) (cutoff : Fin p.T)
    (outcome : CoordinatorRoundDispatch.CollectionOutcome
      (ReferenceActivePhysicalStep.collectionInput x payload ledger clock cutoff))
    (hcoord : (ReferenceActivePhysicalStep.prepare x).coordinator =
      .collection payload ledger clock cutoff outcome) :
    ∃ proposal : Option (Fin p.T × Bool),
      x.state.coordinator = .collection payload ledger proposal := by
  have hdispatch : ReferenceActivePhysicalStep.dispatch x =
      .collection payload ledger clock cutoff outcome := by
    calc
      ReferenceActivePhysicalStep.dispatch x =
          (ReferenceActivePhysicalStep.prepare x).coordinator :=
        (ReferenceActivePhysicalStep.prepare x).coordinator_eq.symm
      _ = .collection payload ledger clock cutoff outcome := hcoord
  cases hphase : x.state.coordinator with
  | first =>
      cases hraw : CoordinatorRoundDispatch.dispatch
          (.first (ReferenceActivePhysicalStep.firstInput x)) with
      | first sourceOutcome =>
          have heq := hdispatch
          simp only [ReferenceActivePhysicalStep.dispatch, hphase, hraw] at heq
          cases heq
  | live registers owned base =>
      cases hraw : CoordinatorRoundDispatch.dispatch
          (.live (ReferenceActivePhysicalStep.liveInput x registers owned base)) with
      | live sourceOutcome =>
          have heq := hdispatch
          simp only [ReferenceActivePhysicalStep.dispatch, hphase, hraw] at heq
          cases heq
  | dagger =>
      simp [ReferenceActivePhysicalStep.dispatch, hphase] at hdispatch
  | collection sourcePayload sourceLedger proposal =>
      by_cases hcutoff : 1 ≤ sourceLedger.cutoff ∧ sourceLedger.cutoff ≤ p.T
      · let sourceCutoff : Fin p.T := ⟨sourceLedger.cutoff - 1, by omega⟩
        let sourceClock := ReferenceActivePhysicalStep.collectionClock
          sourcePayload sourceLedger proposal sourceCutoff
        cases hraw : CoordinatorRoundDispatch.dispatch
            (.collection (ReferenceActivePhysicalStep.collectionInput x sourcePayload
              sourceLedger sourceClock sourceCutoff)) with
        | collection sourceOutcome =>
            have hfields : sourcePayload = payload ∧ sourceLedger = ledger := by
              have hEq := hdispatch
              simp only [ReferenceActivePhysicalStep.dispatch, hphase, dite_eq_left hcutoff,
                sourceCutoff, sourceClock, hraw] at hEq
              injection hEq with hp hl hclock hcut hout
              exact ⟨hp, hl⟩
            rcases hfields with ⟨rfl, rfl⟩
            exact ⟨proposal, rfl⟩
      · simp [ReferenceActivePhysicalStep.dispatch, hphase, hcutoff] at hdispatch

/-- Inverting a retained diagnostic recovers the exact successful recorder
and stage-(1) calls feeding the real collection receiver. -/
private theorem record_retained_up_receiver
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (d : ReferenceActivePhysicalStep.UpDiagnostic p rate)
    (hd : r.output.coordinator.up = some d) :
    ∃ (payload : ReferenceActivePhysicalStep.Payload rate)
      (baseLedger : ReferenceActivePhysicalStep.Ledger rate)
      (started : CoordinatorPhaseClock.StartRoundResult p)
      (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ)
      (recording : CoordinatorRecordingOperation.Output p)
      (ledgerStarted : ReferenceActivePhysicalStep.Ledger rate),
      siteLedger? (x := r.input) = some ledgerStarted ∧
      (baseLedger.pending = Finset.univ ∨
        ∃ proposal : Option (Fin p.T × Bool),
          r.input.state.coordinator = .collection payload baseLedger proposal) ∧
      CoordinatorRecorderComplementBridge.run
        (ReferenceActivePhysicalStep.collectionRecordingInput
          (ReferenceActivePhysicalStep.prepare r.input) payload started weights) =
            some recording ∧
      CoordinatorCollectionLedger.startRound baseLedger (r.input.time.val + 1)
        (ReferenceActivePhysicalStep.collectionEnabled baseLedger r.input.time)
        (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) =
          .success ledgerStarted ∧
      (ReferenceActivePhysicalStep.receiveUp
        (ReferenceActivePhysicalStep.prepare r.input) ledgerStarted).diagnostic = some d ∧
      r.output.next.upDecoderBank =
        (ReferenceActivePhysicalStep.collectionFinish (x := r.input) payload started recording
          (ReferenceActivePhysicalStep.receiveUp
            (ReferenceActivePhysicalStep.prepare r.input) ledgerStarted)).upDecoderBank := by
  have hstep : r.output.coordinator.up =
      (ReferenceActivePhysicalStep.prepare r.input).observeCoordinator.up := by
    rw [r.output_eq]
    rfl
  rw [hstep] at hd
  classical
  let x := r.input
  let prepared := ReferenceActivePhysicalStep.prepare x
  cases hcoord : prepared.coordinator with
  | first outcome =>
      cases outcome with
      | choiceDomainFailure installation =>
          simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
            prepared, x, hcoord, ReferenceActivePhysicalStep.coordinatorFailure] at hd
      | recorderBoundaryFailure installation =>
          simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
            prepared, x, hcoord, ReferenceActivePhysicalStep.coordinatorFailure] at hd
      | choiceRejected installation =>
          simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
            prepared, x, hcoord, ReferenceActivePhysicalStep.coordinatorFailure] at hd
      | chosen installation selected =>
          by_cases hsel :
              ReferenceActivePhysicalStep.DispatchCut.selection
                (.first (.chosen installation selected)) = none
          · simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
              prepared, x, hcoord, hsel, ReferenceActivePhysicalStep.coordinatorFailure] at hd
          · have heq := ReferenceActivePhysicalStep.observeCoordinator_first_equation
              prepared (.chosen installation selected) hcoord
            rw [heq, ite_eq_right hsel] at hd
            dsimp at hd
            unfold ReferenceActivePhysicalStep.livePostChoice at hd
            repeat' (first | split at hd | simp [ReferenceActivePhysicalStep.coordinatorFailure] at hd)
  | live registers owned base outcome =>
      cases outcome with
      | clockFailure failure _ =>
          simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
            prepared, x, hcoord, ReferenceActivePhysicalStep.coordinatorFailure] at hd
      | initializerFailure dispatched _ _ _ =>
          simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
            prepared, x, hcoord, ReferenceActivePhysicalStep.coordinatorFailure] at hd
      | localFailure dispatched _ reason =>
          simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
            prepared, x, hcoord, ReferenceActivePhysicalStep.coordinatorFailure] at hd
      | cutoffChosen dispatched hstart ledger hinit hledger hdomain hclock hpending
          hnoassignment selected =>
          by_cases hsel :
              ReferenceActivePhysicalStep.DispatchCut.selection
                (.live registers owned base
                  (.cutoffChosen dispatched hstart ledger hinit hledger hdomain hclock
                    hpending hnoassignment selected)) = none
          · simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
              prepared, x, hcoord, hsel, ReferenceActivePhysicalStep.coordinatorFailure] at hd
          · let payload := registers.payload
            let baseLedger := ReferenceActivePhysicalStep.sharedLedger ledger
            let started := dispatched.startResult
            let weights :=
              (ReferenceActivePhysicalStep.liveRegistersAt registers x.time).complementWeights
            have heq := ReferenceActivePhysicalStep.observeCoordinator_live_equation
              prepared registers owned base
              (.cutoffChosen dispatched hstart ledger hinit hledger hdomain hclock
                hpending hnoassignment selected) hcoord
            rw [heq, ite_eq_right hsel] at hd
            change (ReferenceActivePhysicalStep.collectionPostChoice prepared payload
              baseLedger started weights).up = some d at hd
            obtain ⟨ledgerStarted, htail, hcheck, hinput, hafter⟩ :=
              collectionPostChoice_up_input x payload baseLedger started weights d hd
            obtain ⟨recording, hrecording, hstartRound⟩ :=
              tailLedger?_success x prepared payload baseLedger started weights ledgerStarted htail
            have hpost := ReferenceActivePhysicalStep.collectionPostChoice_after_start
              prepared payload baseLedger started weights recording ledgerStarted hrecording hstartRound
            have hbasePending : baseLedger.pending = Finset.univ := by
              simp [baseLedger, ReferenceActivePhysicalStep.sharedLedger, hledger,
                CoordinatorStartRoundCutoffDispatch.collectionStartLedger]
            have hreceiveDiagnostic :
                (ReferenceActivePhysicalStep.receiveUp prepared ledgerStarted).diagnostic = some d := by
              rw [hpost, ReferenceActiveAffinePositiveTest.collectionFinish_up] at hd
              exact hd
            have hobs : prepared.observeCoordinator =
                ReferenceActivePhysicalStep.collectionPostChoice prepared payload baseLedger
                  started weights := by
              rw [heq, ite_eq_right hsel]
            have hnext : r.output.next.upDecoderBank =
                    (ReferenceActivePhysicalStep.collectionFinish (x := x) payload started recording
                  (ReferenceActivePhysicalStep.receiveUp prepared ledgerStarted)).upDecoderBank := by
              calc
                r.output.next.upDecoderBank =
                    (ReferenceActivePhysicalStep.step x).next.upDecoderBank := by rw [r.output_eq]
                _ = prepared.observeCoordinator.upDecoderBank :=
                    (ReferenceActivePhysicalStep.step_next_fields x).2.1
                _ = (ReferenceActivePhysicalStep.collectionPostChoice prepared payload
                      baseLedger started weights).upDecoderBank :=
                    congrArg ReferenceActivePhysicalStep.CoordinatorObservation.upDecoderBank hobs
                _ = (ReferenceActivePhysicalStep.collectionFinish (x := x) payload started recording
                      (ReferenceActivePhysicalStep.receiveUp prepared ledgerStarted)).upDecoderBank :=
                    congrArg ReferenceActivePhysicalStep.CoordinatorObservation.upDecoderBank hpost
            refine ⟨payload, baseLedger, started, weights, recording, ledgerStarted, ?_,
              Or.inl hbasePending, hrecording, hstartRound, hreceiveDiagnostic, hnext⟩
            simpa [siteLedger?, prepared, x, hcoord, hsel, payload, baseLedger, started, weights] using htail
      | continuingChosen dispatched startRoundEq continuation selected =>
          by_cases hsel :
              ReferenceActivePhysicalStep.DispatchCut.selection
                (.live registers owned base
                  (.continuingChosen dispatched startRoundEq continuation selected)) = none
          · simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
              prepared, x, hcoord, hsel, ReferenceActivePhysicalStep.coordinatorFailure] at hd
          · have heq := ReferenceActivePhysicalStep.observeCoordinator_live_equation
              prepared registers owned base
              (.continuingChosen dispatched startRoundEq continuation selected) hcoord
            rw [heq, ite_eq_right hsel] at hd
            dsimp at hd
            unfold ReferenceActivePhysicalStep.livePostChoice at hd
            repeat' (first | split at hd | simp [ReferenceActivePhysicalStep.coordinatorFailure] at hd)
  | collection payload ledger clock cutoff outcome =>
      cases outcome with
      | clockFailure failure _ =>
          simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
            prepared, x, hcoord, ReferenceActivePhysicalStep.coordinatorFailure] at hd
      | localFailure started _ _ =>
          simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
            prepared, x, hcoord, ReferenceActivePhysicalStep.coordinatorFailure] at hd
      | coreFailure core started _ _ =>
          simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
            prepared, x, hcoord, ReferenceActivePhysicalStep.coordinatorFailure] at hd
      | continuing core snapshot boundary scores =>
          by_cases hsel :
              ReferenceActivePhysicalStep.DispatchCut.selection
                (.collection payload ledger clock cutoff
                  (.continuing core snapshot boundary scores)) = none
          · simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
              prepared, x, hcoord, hsel, ReferenceActivePhysicalStep.coordinatorFailure] at hd
          · let source := ReferenceActivePhysicalStep.collectionInput x payload ledger clock cutoff
            let weights := CoordinatorCollectionInteractive.PreObservationInputs.weights source
              snapshot.inputsValid.ledger_valid snapshot.inputsValid.assignment_eq
            have heq := ReferenceActivePhysicalStep.observeCoordinator_collection_equation
              prepared payload ledger clock cutoff (.continuing core snapshot boundary scores) hcoord
            rw [heq, ite_eq_right hsel] at hd
            change (ReferenceActivePhysicalStep.collectionPostChoice prepared payload ledger
              snapshot.clockStarted weights).up = some d at hd
            obtain ⟨ledgerStarted, htail, hcheck, hinput, hafter⟩ :=
              collectionPostChoice_up_input x payload ledger snapshot.clockStarted weights d hd
            obtain ⟨recording, hrecording, hstartRound⟩ :=
              tailLedger?_success x prepared payload ledger snapshot.clockStarted weights
                ledgerStarted htail
            have hpost := ReferenceActivePhysicalStep.collectionPostChoice_after_start
              prepared payload ledger snapshot.clockStarted weights recording ledgerStarted
              hrecording hstartRound
            obtain ⟨proposal, hsource⟩ := sourceCollection_of_preparedCollection x payload ledger
              clock cutoff (.continuing core snapshot boundary scores) hcoord
            have hreceiveDiagnostic :
                (ReferenceActivePhysicalStep.receiveUp prepared ledgerStarted).diagnostic = some d := by
              rw [hpost, ReferenceActiveAffinePositiveTest.collectionFinish_up] at hd
              exact hd
            have hobs : prepared.observeCoordinator =
                ReferenceActivePhysicalStep.collectionPostChoice prepared payload ledger
                  snapshot.clockStarted weights := by
              rw [heq, ite_eq_right hsel]
            have hnext : r.output.next.upDecoderBank =
                    (ReferenceActivePhysicalStep.collectionFinish (x := x) payload snapshot.clockStarted recording
                  (ReferenceActivePhysicalStep.receiveUp prepared ledgerStarted)).upDecoderBank := by
              calc
                r.output.next.upDecoderBank =
                    (ReferenceActivePhysicalStep.step x).next.upDecoderBank := by rw [r.output_eq]
                _ = prepared.observeCoordinator.upDecoderBank :=
                    (ReferenceActivePhysicalStep.step_next_fields x).2.1
                _ = (ReferenceActivePhysicalStep.collectionPostChoice prepared payload ledger
                      snapshot.clockStarted weights).upDecoderBank :=
                    congrArg ReferenceActivePhysicalStep.CoordinatorObservation.upDecoderBank hobs
                _ = (ReferenceActivePhysicalStep.collectionFinish (x := x) payload snapshot.clockStarted recording
                      (ReferenceActivePhysicalStep.receiveUp prepared ledgerStarted)).upDecoderBank :=
                    congrArg ReferenceActivePhysicalStep.CoordinatorObservation.upDecoderBank hpost
            refine ⟨payload, ledger, snapshot.clockStarted, weights, recording, ledgerStarted,
              ?_, Or.inr ⟨proposal, hsource⟩, hrecording, hstartRound, hreceiveDiagnostic, hnext⟩
            simpa [siteLedger?, prepared, x, hcoord, hsel, source, weights] using htail
      | laterReconstructionFailure core consistent started _ instruction _ _ =>
          simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
            prepared, x, hcoord, ReferenceActivePhysicalStep.coordinatorFailure] at hd
      | laterPrefixFailure core consistent started _ instruction _ _ _ =>
          simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
            prepared, x, hcoord, ReferenceActivePhysicalStep.coordinatorFailure] at hd
      | laterOrientationFailure core consistent started _ instruction _ _ =>
          simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
            prepared, x, hcoord, ReferenceActivePhysicalStep.coordinatorFailure] at hd
      | laterChoiceFailure core consistent started startRoundEq instruction assignmentStartEq
          output localEq clockData installed reason =>
          simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
            prepared, x, hcoord, ReferenceActivePhysicalStep.coordinatorFailure] at hd
      | laterChosen core consistent started startRoundEq instruction assignmentStartEq output
          localEq clockData installed selected =>
          by_cases hsel :
              ReferenceActivePhysicalStep.DispatchCut.selection
                (.collection payload ledger clock cutoff
                  (.laterChosen core consistent started startRoundEq instruction assignmentStartEq
                    output localEq clockData installed selected)) = none
          · simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
              prepared, x, hcoord, hsel, ReferenceActivePhysicalStep.coordinatorFailure] at hd
          · have heq := ReferenceActivePhysicalStep.observeCoordinator_collection_equation
              prepared payload ledger clock cutoff
              (.laterChosen core consistent started startRoundEq instruction assignmentStartEq
                output localEq clockData installed selected) hcoord
            rw [heq, ite_eq_right hsel] at hd
            dsimp at hd
            unfold ReferenceActivePhysicalStep.livePostChoice at hd
            repeat' (first | split at hd | simp [ReferenceActivePhysicalStep.coordinatorFailure] at hd)
  | invalidCollectionCutoff =>
      simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
        prepared, x, hcoord, ReferenceActivePhysicalStep.DispatchCut.selection,
        ReferenceActivePhysicalStep.coordinatorFailure] at hd
  | dagger =>
      simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
        prepared, x, hcoord, ReferenceActivePhysicalStep.DispatchCut.selection] at hd

private theorem collectionFinish_result_bank
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (recording : CoordinatorRecordingOperation.Output p)
    (cut : ReferenceActivePhysicalStep.UpCut p rate)
    (out : ReferenceActivePhysicalStep.Ledger rate × CoordinatorUpReception.UpDecoderBank p)
    (hresult : cut.result = .success out ∨ cut.result = .rejected out) :
    (ReferenceActivePhysicalStep.collectionFinish (x := x) payload started recording cut).upDecoderBank = out.2 := by
  rcases hresult with hsuccess | hrejected
  · cases hfinish : CoordinatorCollectionLedger.finishRound out.1 with
    | invalid => simp [ReferenceActivePhysicalStep.collectionFinish, hsuccess, hfinish,
        ReferenceActivePhysicalStep.coordinatorFailure]
    | rejected ignored => simp [ReferenceActivePhysicalStep.collectionFinish, hsuccess, hfinish,
        ReferenceActivePhysicalStep.coordinatorFailure]
    | success ledgerFinished =>
        cases hclock : CoordinatorPhaseClock.finishRound p rate.eta.val x.time
            started.clock ledgerFinished.pending x.row with
        | error reason =>
            simp [ReferenceActivePhysicalStep.collectionFinish, hsuccess, hfinish, hclock,
              ReferenceActivePhysicalStep.coordinatorFailure]
        | ok clockFinished =>
            simp [ReferenceActivePhysicalStep.collectionFinish, hsuccess, hfinish, hclock]
  · cases hfinish : CoordinatorCollectionLedger.finishRound out.1 with
    | invalid => simp [ReferenceActivePhysicalStep.collectionFinish, hrejected, hfinish,
        ReferenceActivePhysicalStep.coordinatorFailure]
    | rejected ignored => simp [ReferenceActivePhysicalStep.collectionFinish, hrejected, hfinish,
        ReferenceActivePhysicalStep.coordinatorFailure]
    | success ledgerFinished =>
        cases hclock : CoordinatorPhaseClock.finishRound p rate.eta.val x.time
            started.clock ledgerFinished.pending x.row with
        | error reason =>
            simp [ReferenceActivePhysicalStep.collectionFinish, hrejected, hfinish, hclock,
              ReferenceActivePhysicalStep.coordinatorFailure]
        | ok clockFinished =>
            simp [ReferenceActivePhysicalStep.collectionFinish, hrejected, hfinish, hclock]

/-- The record-facing commitment cases use only the phase-indexed invariant
on the record's original state. Invalid reception frames the old bank;
success and ordinary rejection carry the exact bank returned by the actual
filtered receiver, even when a later finish operation produces dagger. -/
theorem record_up_commit_cases
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (d : ReferenceActivePhysicalStep.UpDiagnostic p rate)
    (hd : r.output.coordinator.up = some d)
    (hinvariant : ReferenceUpDecoderBankInvariant.upBankInvariant r.input.state) :
    ∃ ledger, siteLedger? (x := r.input) = some ledger ∧
      CoordinatorUpReception.receptionInputCheck (actualUpInput r.input ledger) = true ∧
      d.input = actualUpInput r.input ledger ∧
      d.decoderAfter = (CoordinatorUpReception.decoderTransition
        (actualUpInput r.input ledger)).1 ∧
      ((ReferenceActivePhysicalStep.receiveUp
          (ReferenceActivePhysicalStep.prepare r.input) ledger).result = .invalid ∧
          r.output.next.upDecoderBank = r.input.state.upDecoderBank ∨
        ∃ out,
          ((ReferenceActivePhysicalStep.receiveUp
              (ReferenceActivePhysicalStep.prepare r.input) ledger).result = .success out ∨
            (ReferenceActivePhysicalStep.receiveUp
              (ReferenceActivePhysicalStep.prepare r.input) ledger).result = .rejected out) ∧
          out.2 = CoordinatorUpReception.decoderBankAfter d.input ∧
          r.output.next.upDecoderBank = out.2) := by
  obtain ⟨payload, baseLedger, started, weights, recording, ledgerStarted,
      hsite, hsource, hrecording, hstart, hreceiveDiagnostic, hnext⟩ :=
    record_retained_up_receiver r d hd
  obtain ⟨siteLedger, hsiteInput, hcheck, hinput, hafter⟩ :=
    record_retained_up_input r d hd
  have hsame : siteLedger = ledgerStarted := by
    have hsome : some siteLedger = some ledgerStarted :=
      hsiteInput.symm.trans hsite
    exact Option.some.inj hsome
  subst siteLedger
  have hstartedPending : ledgerStarted.pending = baseLedger.pending := by
    rw [ReferenceActivePhysicalStep.collection_started_candidate baseLedger ledgerStarted
      r.input.time (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) hstart]
    rfl
  have hpending : ∀ i, i ∉ ledgerStarted.pending →
      (r.input.state.upDecoderBank i).pending = [] := by
    rcases hsource with hfull | ⟨proposal, hphase⟩
    · intro i hi
      simp [hstartedPending, hfull] at hi
    · have hlocal := hinvariant
      simp [ReferenceUpDecoderBankInvariant.upBankInvariant,
        ReferenceUpDecoderBankInvariant.coordinatorBankInvariant, hphase] at hlocal
      rcases hlocal with ⟨_, hlocal⟩
      intro i hi
      apply hlocal i
      simpa [hstartedPending] using hi
  let prepared := ReferenceActivePhysicalStep.prepare r.input
  let cut := ReferenceActivePhysicalStep.receiveUp prepared ledgerStarted
  refine ⟨ledgerStarted, hsite, hcheck, hinput, hafter, ?_⟩
  cases hresult : cut.result with
  | invalid =>
      have hbankCases := ReferenceUpDecoderBankInvariant.collectionFinish_upDecoderBank_alternatives
        (x := r.input) payload started recording cut
      rcases hbankCases with hframe | ⟨out, hout, hcommitted⟩
      · exact Or.inl ⟨rfl, hnext.trans hframe⟩
      · rcases hout with hs | hr
        · rw [hresult] at hs
          cases hs
        · rw [hresult] at hr
          cases hr
  | success out =>
      have hreceive := ReferenceCoordinatorUpDecoderReplay.receiveUp_actual_diagnostic_and_replay
        prepared ledgerStarted hpending out (Or.inl hresult)
      have hinputReceive := hreceive.1
      rw [hreceiveDiagnostic] at hinputReceive
      simp only [Option.map_some] at hinputReceive
      have hafterReceive := hreceive.2.1
      rw [hreceiveDiagnostic] at hafterReceive
      simp only [Option.map_some] at hafterReceive
      have hbankAfter := ReferenceUpDecoderBankInvariant.actualFilteredReceive_decoderBankAfter
        prepared ledgerStarted hpending out (Or.inl hresult)
      have hbankAfter' : out.2 = CoordinatorUpReception.decoderBankAfter d.input := by
        simpa [hinput, actualUpInput, ReferenceActivePhysicalStep.upInputs] using hbankAfter
      have hfinishBank := collectionFinish_result_bank (x := r.input) payload started recording cut out
        (Or.inl hresult)
      have hnextBank : r.output.next.upDecoderBank = out.2 := hnext.trans hfinishBank
      exact Or.inr ⟨out, Or.inl rfl, hbankAfter', hnextBank⟩
  | rejected out =>
      have hreceive := ReferenceCoordinatorUpDecoderReplay.receiveUp_actual_diagnostic_and_replay
        prepared ledgerStarted hpending out (Or.inr hresult)
      have hinputReceive := hreceive.1
      rw [hreceiveDiagnostic] at hinputReceive
      simp only [Option.map_some] at hinputReceive
      have hafterReceive := hreceive.2.1
      rw [hreceiveDiagnostic] at hafterReceive
      simp only [Option.map_some] at hafterReceive
      have hbankAfter := ReferenceUpDecoderBankInvariant.actualFilteredReceive_decoderBankAfter
        prepared ledgerStarted hpending out (Or.inr hresult)
      have hbankAfter' : out.2 = CoordinatorUpReception.decoderBankAfter d.input := by
        simpa [hinput, actualUpInput, ReferenceActivePhysicalStep.upInputs] using hbankAfter
      have hfinishBank := collectionFinish_result_bank (x := r.input) payload started recording cut out
        (Or.inr hresult)
      have hnextBank : r.output.next.upDecoderBank = out.2 := hnext.trans hfinishBank
      exact Or.inr ⟨out, Or.inr rfl, hbankAfter', hnextBank⟩

/-- A record in the canonical physical run keeps the original complete row
table, fixed selected row, and reward table. Its retained-call statements are
derived from the single initial bank invariant through the actual run, rather
than from a caller-supplied record invariant. -/
theorem run_record_up_input
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p)
    (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hinitial : ReferenceUpDecoderBankInvariant.upBankInvariant initial)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hrecord : r ∈ (ReferenceActivePhysicalHorizon.run initial rows selected rewards
      start count hspan hmode).records) :
    r.input.rows = rows ∧ r.input.selected = selected ∧ r.input.rewards = rewards ∧
      ReferenceUpDecoderBankInvariant.upBankInvariant r.input.state ∧
      ((∃ d, r.output.coordinator.up = some d) ↔
        ∃ ledger, siteLedger? (x := r.input) = some ledger ∧
          CoordinatorUpReception.receptionInputCheck (actualUpInput r.input ledger) = true) ∧
      (∀ d, (hd : r.output.coordinator.up = some d) →
        (∃ ledger, siteLedger? (x := r.input) = some ledger ∧
          CoordinatorUpReception.receptionInputCheck (actualUpInput r.input ledger) = true ∧
          d.input = actualUpInput r.input ledger ∧
          d.decoderAfter = (CoordinatorUpReception.decoderTransition
            (actualUpInput r.input ledger)).1) ∧
        (∃ ledger, siteLedger? (x := r.input) = some ledger ∧
          d.input.ledger = ledger ∧
          d.input.upDecoderBank = r.input.state.upDecoderBank ∧
          d.input.time = r.input.time ∧
          d.input.ownObservation =
            (ReferenceActivePhysicalStep.prepare r.input).feedback.feedback
              (ActiveRoundActions.coordinator p.two_le_m) ∧
          d.input.selectedFollower =
            CoordinatorUpMeasurability.selectedFollowerIndex
              ((r.input.rows r.input.selected).2 r.input.time) ∧
          d.input.affineSample =
            ((r.input.rows r.input.selected).2 r.input.time).2
              (1, CoordinatorUpMeasurability.selectedChannelFollower
                ((r.input.rows r.input.selected).2 r.input.time)) ∧
          d.input.slot = PublicDiscreteDraws.slotDraw
            ((r.input.rows r.input.selected).2 r.input.time).1 ∧
          (CoordinatorUpReception.roundInput d.input).receiverEnabled = true ∧
          (CoordinatorUpReception.roundInput d.input).selected = decide
            (ledger.cutoff ≤ r.input.time.val + 1 ∧
              d.input.slot = PublicDiscreteDraws.upSlot ∧
              d.input.selectedFollower ∈ ledger.pending) ∧
          (CoordinatorUpReception.roundInput d.input).sample = d.input.affineSample ∧
          (CoordinatorUpReception.roundInput d.input).roundedReward =
            CoordinatorUpReception.roundedObservationValue p
              ((ReferenceActivePhysicalStep.prepare r.input).feedback.feedback
                (ActiveRoundActions.coordinator p.two_le_m)) ∧
          (ReferenceActivePhysicalStep.prepare r.input).feedback.feedback
              (ActiveRoundActions.coordinator p.two_le_m) =
            if FiniteBanditModel.collisionFreeFor
                (ReferenceActivePhysicalStep.prepare r.input).arms.actions
                  (ActiveRoundActions.coordinator p.two_le_m) then
              r.input.rewards r.input.time
                ((ReferenceActivePhysicalStep.prepare r.input).arms.actions
                  (ActiveRoundActions.coordinator p.two_le_m))
            else 0)) ∧
      r.output.ownEntries (ActiveRoundActions.coordinator p.two_le_m) =
        (r.output.preparation.arms.actions
            (ActiveRoundActions.coordinator p.two_le_m),
          ActualInitializationPhysicalStep.observationOfGrid p
            (r.output.preparation.feedback.feedback
              (ActiveRoundActions.coordinator p.two_le_m))) := by
  have hrecordInv := ReferenceUpDecoderBankInvariant.run_record_input_upBankInvariant
    initial rows selected rewards start count hspan hmode hinitial r hrecord
  have hinputs := ReferenceActivePhysicalHorizon.run_record_inputs
    initial rows selected rewards start count hspan hmode r hrecord
  rcases hinputs with ⟨hrows, hselected, hrewards⟩
  refine ⟨hrows, hselected, hrewards, hrecordInv, ?_, ?_, ?_⟩
  · exact record_up_retention_iff r
  · intro d hd
    exact ⟨record_retained_up_input r d hd,
      record_retained_up_input_fields r d hd⟩
  · exact record_retained_up_own_entry r

/-- Commit cases for a member of the same computed run. The only supplied
invariant is at the run's initial state; the per-record invariant is obtained
from the canonical record-input induction. -/
theorem run_record_up_commit
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p)
    (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hinitial : ReferenceUpDecoderBankInvariant.upBankInvariant initial)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hrecord : r ∈ (ReferenceActivePhysicalHorizon.run initial rows selected rewards
      start count hspan hmode).records) :
    r.input.rows = rows ∧ r.input.selected = selected ∧ r.input.rewards = rewards ∧
      ReferenceUpDecoderBankInvariant.upBankInvariant r.input.state ∧
      ∀ d, (hd : r.output.coordinator.up = some d) →
        ∃ ledger, siteLedger? (x := r.input) = some ledger ∧
          CoordinatorUpReception.receptionInputCheck (actualUpInput r.input ledger) = true ∧
          d.input = actualUpInput r.input ledger ∧
          d.decoderAfter = (CoordinatorUpReception.decoderTransition
            (actualUpInput r.input ledger)).1 ∧
          ((ReferenceActivePhysicalStep.receiveUp
              (ReferenceActivePhysicalStep.prepare r.input) ledger).result = .invalid ∧
              r.output.next.upDecoderBank = r.input.state.upDecoderBank ∨
            ∃ out,
              ((ReferenceActivePhysicalStep.receiveUp
                  (ReferenceActivePhysicalStep.prepare r.input) ledger).result = .success out ∨
                (ReferenceActivePhysicalStep.receiveUp
                  (ReferenceActivePhysicalStep.prepare r.input) ledger).result = .rejected out) ∧
              out.2 = CoordinatorUpReception.decoderBankAfter d.input ∧
              r.output.next.upDecoderBank = out.2) := by
  have hrecordInv := ReferenceUpDecoderBankInvariant.run_record_input_upBankInvariant
    initial rows selected rewards start count hspan hmode hinitial r hrecord
  have hinputs := ReferenceActivePhysicalHorizon.run_record_inputs
    initial rows selected rewards start count hspan hmode r hrecord
  rcases hinputs with ⟨hrows, hselected, hrewards⟩
  refine ⟨hrows, hselected, hrewards, hrecordInv, ?_⟩
  intro d hd
  exact record_up_commit_cases r d hd hrecordInv

/-- The actual launched boundary supplies the initial state and its sole UP
bank invariant. Every conclusion is about a member of the same canonical run
over the original complete rows, selected row, rewards, and calendar interval.
The source block-stop bound supplies the run's active-mode proof. -/
theorem actualLaunched_run_record_up_commit
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (rate : ActualInitializationLaunchState.RateInput p)
    (C_star C_h : ℝ) (b : ReferenceInitializationRun.Boundary p)
    (h : b.completed < BootstrapDimensions.n_boot p)
    (actual : ActualInitializationRun.BlockCarry p rate
      (ReferenceInitializationRun.nextBlock b h))
    (past : List (ActualInitializationRun.PhysicalRoundRecord p rate source rewards))
    (hr : ActualReferenceInitializationBlock.BlockStartRelated source rewards
      C_star C_h rate (ReferenceInitializationRun.nextBlock b h) actual b past)
    (hdown : ∀ i, ¬ InitializationFailureProvenance.generatedBlockDown
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate) b h i)
    (hclean : ∀ (i : Fin (p.m - 1))
      (hi : ActualReferenceInitializationBlock.refFollower i ∈
        (ReferenceInitializationRun.physical
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate) b h).uninformed),
      BootstrapAllCandidateController.cleanPrefix
        (ReferenceInitializationRun.physical
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate) b h)
        source.1.2 ⟨ActualReferenceInitializationBlock.refFollower i, hi⟩
        (ActualInitializationPhysicalStep.selectedRowIndex p source) p.T)
    (hforce : ∀ i, ReferenceInitializationRun.forced
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate) b h i = false)
    (launch : BootstrapCoordinatorLocalRound.LaunchedBlock p)
    (learnerSeed : ActualInitializationRun.CoordinatorLearnerZeroSeed p)
    (hlaunched : (ActualInitializationRun.combinedBoundaryHandoff p rate
      (ReferenceInitializationRun.nextBlock b h) source rewards actual.C_star actual.C_h
      (ActualInitializationRun.foldBlock p rate (ReferenceInitializationRun.nextBlock b h)
        source rewards actual)).disposition = .launched launch learnerSeed)
    (start count : ℕ)
    (hstart : BootstrapObservedFollower.blockStop p
      (ReferenceInitializationRun.nextBlock b h) ≤ start)
    (hspan : start + count ≤ p.T)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hrecord : r ∈ (ReferenceActivePhysicalHorizon.run
      (ActualInitializationLaunchState.ofActualLaunchedBoundary source rewards rate C_star C_h
        b h actual past hr hdown hclean hforce launch learnerSeed hlaunched)
      source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
      start count hspan
      (by
        intro i
        have hactivation :=
          ActualInitializationLaunchState.ofActualLaunchedBoundary_activation_le_blockStop
            source rewards rate C_star C_h b h actual past hr hdown hclean hforce launch
            learnerSeed hlaunched i
        omega)).records) :
    r.input.rows = source.1.2 ∧
      r.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p source ∧
      r.input.rewards = rewards ∧
      ReferenceUpDecoderBankInvariant.upBankInvariant r.input.state ∧
      ∀ d, (hd : r.output.coordinator.up = some d) →
        ∃ ledger, siteLedger? (x := r.input) = some ledger ∧
          CoordinatorUpReception.receptionInputCheck (actualUpInput r.input ledger) = true ∧
          d.input = actualUpInput r.input ledger ∧
          d.decoderAfter = (CoordinatorUpReception.decoderTransition
            (actualUpInput r.input ledger)).1 ∧
          ((ReferenceActivePhysicalStep.receiveUp
              (ReferenceActivePhysicalStep.prepare r.input) ledger).result = .invalid ∧
              r.output.next.upDecoderBank = r.input.state.upDecoderBank ∨
            ∃ out,
              ((ReferenceActivePhysicalStep.receiveUp
                  (ReferenceActivePhysicalStep.prepare r.input) ledger).result = .success out ∨
                (ReferenceActivePhysicalStep.receiveUp
                  (ReferenceActivePhysicalStep.prepare r.input) ledger).result = .rejected out) ∧
              out.2 = CoordinatorUpReception.decoderBankAfter d.input ∧
              r.output.next.upDecoderBank = out.2) := by
  let initial := ActualInitializationLaunchState.ofActualLaunchedBoundary source rewards rate
    C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed hlaunched
  have hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start := by
    intro i
    have hactivation :=
      ActualInitializationLaunchState.ofActualLaunchedBoundary_activation_le_blockStop
        source rewards rate C_star C_h b h actual past hr hdown hclean hforce launch
        learnerSeed hlaunched i
    have hactivation' : (initial.activations i).val ≤
        BootstrapObservedFollower.blockStop p (ReferenceInitializationRun.nextBlock b h) + 1 := by
      simpa [initial] using hactivation
    omega
  have hinitial := ReferenceUpDecoderBankInvariant.ofActualLaunchedBoundary_upBankInvariant
    source rewards rate C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed
    hlaunched
  exact run_record_up_commit initial source.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start count hspan
    hmode hinitial r hrecord

end Bandits.Support.ReferenceCoordinatorUpPhysicalCall

end
