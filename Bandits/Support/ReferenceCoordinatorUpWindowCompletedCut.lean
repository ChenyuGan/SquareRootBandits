/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCoordinatorUpIntervalWindow

import Mathlib.Data.List.TakeDrop
import Lean.Elab.Tactic.Omega

/-!
# Saved physical provenance for a completed UP window

Sources: `sources/zip4/manuscript/05_binary_transport.tex:36-53,70-124`,
`sources/zip4/manuscript/06_interruptions.tex:277-284,327-348`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:92-109,151-157`.

This module connects the interval decoder's actual second completed batch to
the retained diagnostic at that same physical call. It uses the actual run
prefix and exhaustive retained-diagnostic replay to identify the pre-call
bank, then exposes both the completed decoder transition and the saved raw
output. It assumes only the interval module's explicit geometry conditions;
it does not assert that the call is an awaited or accepted UP message.
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
open Bandits.Support.ReferenceCoordinatorUpIntervalWindow

namespace Bandits.Support.ReferenceCoordinatorUpWindowCompletedCut

local instance propDecidable (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition

abbrev Parameters := ReferenceCoordinatorUpIntervalWindow.Parameters
abbrev RateInput := ReferenceCoordinatorUpIntervalWindow.RateInput

variable {p : Parameters} {rate : RateInput p}

private theorem connected_append_split
    {initial final : ReferenceActivePhysicalStep.State p rate}
    (left right : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (hchain : ReferenceActivePhysicalHorizon.Connected initial (left ++ right) final) :
    ∃ middle, ReferenceActivePhysicalHorizon.Connected initial left middle ∧
      ReferenceActivePhysicalHorizon.Connected middle right final := by
  induction left generalizing initial with
  | nil =>
      refine ⟨initial, ?_, ?_⟩
      · simp [ReferenceActivePhysicalHorizon.Connected]
      · simpa using hchain
  | cons head tail ih =>
      simp only [List.cons_append, ReferenceActivePhysicalHorizon.Connected] at hchain ⊢
      rcases hchain with ⟨hhead, htail⟩
      obtain ⟨middle, hleft, hright⟩ := ih htail
      exact ⟨middle, ⟨hhead, hleft⟩, hright⟩

private theorem mem_of_mem_take_list {α : Type} (values : List α) (count : ℕ)
    {value : α} (hvalue : value ∈ values.take count) : value ∈ values := by
  induction count generalizing values with
  | zero => simp at hvalue
  | succ count ih =>
      cases values with
      | nil => simp at hvalue
      | cons head tail =>
          simp only [List.take_succ_cons, List.mem_cons] at hvalue ⊢
          rcases hvalue with hhead | htail
          · exact Or.inl hhead
          · exact Or.inr (ih tail htail)

private theorem mem_of_mem_drop_list {α : Type} (values : List α) (count : ℕ)
    {value : α} (hvalue : value ∈ values.drop count) : value ∈ values := by
  induction count generalizing values with
  | zero => simpa using hvalue
  | succ count ih =>
      cases values with
      | nil => simp at hvalue
      | cons head tail =>
          exact List.mem_cons_of_mem head (ih tail (by simpa using hvalue))

private theorem connected_prefix_upDecoderBank_replay
    {initial final : ReferenceActivePhysicalStep.State p rate}
    {records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))}
    (hchain : ReferenceActivePhysicalHorizon.Connected initial records final)
    (hinvariant : ∀ record, record ∈ records →
      ReferenceUpDecoderBankInvariant.upBankInvariant record.input.state)
    (hordinary : final.coordinator ≠ .dagger) :
    final.upDecoderBank = ReferenceCoordinatorUpDecoderReplay.replay initial.upDecoderBank
      (ReferenceCoordinatorUpDecoderReplay.retainedUpDiagnostics records) := by
  induction records generalizing initial with
  | nil =>
      simp only [ReferenceActivePhysicalHorizon.Connected] at hchain
      subst final
      rfl
  | cons record records ih =>
      simp only [ReferenceActivePhysicalHorizon.Connected] at hchain
      rcases hchain with ⟨hinput, htail⟩
      have hnextOrdinary : record.output.next.coordinator ≠ .dagger := by
        intro hdagger
        exact hordinary
          (ReferenceActivePhysicalHorizon.Connected.coordinator_dagger htail hdagger).1
      have hrecordReplay :=
        ReferenceCoordinatorUpDecoderReplay.ordinaryRecord_upDecoderBank_replay
          record (hinvariant record (by simp)) hnextOrdinary
      have htailInvariant : ∀ current, current ∈ records →
          ReferenceUpDecoderBankInvariant.upBankInvariant current.input.state := by
        intro current hcurrent
        exact hinvariant current (by simp [hcurrent])
      have htailReplay := ih htail htailInvariant
      calc
        final.upDecoderBank = ReferenceCoordinatorUpDecoderReplay.replay
            record.output.next.upDecoderBank
            (ReferenceCoordinatorUpDecoderReplay.retainedUpDiagnostics records) := htailReplay
        _ = ReferenceCoordinatorUpDecoderReplay.replay
            (ReferenceCoordinatorUpDecoderReplay.replayOption initial.upDecoderBank
              record.output.coordinator.up)
            (ReferenceCoordinatorUpDecoderReplay.retainedUpDiagnostics records) := by
              rw [hrecordReplay, hinput]
        _ = ReferenceCoordinatorUpDecoderReplay.replay initial.upDecoderBank
            (ReferenceCoordinatorUpDecoderReplay.retainedUpDiagnostics (record :: records)) := by
              cases hdiagnostic : record.output.coordinator.up <;>
                simp [ReferenceCoordinatorUpDecoderReplay.replay,
                  ReferenceCoordinatorUpDecoderReplay.replayOption,
                  ReferenceCoordinatorUpDecoderReplay.retainedUpDiagnostics, hdiagnostic]

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
      d.decoderAfter = (CoordinatorUpReception.decoderTransition
        (ReferenceCoordinatorUpPhysicalCall.actualUpInput x ledgerStarted)).1 ∧
      d.raw = (CoordinatorUpReception.decoderTransition
        (ReferenceCoordinatorUpPhysicalCall.actualUpInput x ledgerStarted)).2 := by
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
          have hrawSaved := congrArg
            (Option.map ReferenceActivePhysicalStep.UpDiagnostic.raw) hd
          rw [hrawMap] at hrawSaved
          have hraw : d.raw = (CoordinatorUpReception.decoderTransition input).2 :=
            (Option.some.inj hrawSaved).symm
          have hafterSaved := congrArg
            (Option.map ReferenceActivePhysicalStep.UpDiagnostic.decoderAfter) hd
          rw [hafterMap] at hafterSaved
          have hafter : d.decoderAfter = (CoordinatorUpReception.decoderTransition input).1 :=
            (Option.some.inj hafterSaved).symm
          refine ⟨ledgerStarted, htail, ?_, ?_, hafter, ?_⟩
          · simpa [hinput] using hcheck
          · have hinputSaved := congrArg
              (Option.map ReferenceActivePhysicalStep.UpDiagnostic.input) hd
            simp [ReferenceActivePhysicalStep.receiveUp, inputs, input, hcheck] at hinputSaved
            exact hinputSaved.symm.trans hinput
          · simpa [hinput] using hraw

private theorem record_retained_up_transition
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (d : ReferenceActivePhysicalStep.UpDiagnostic p rate)
    (hdiagnostic : record.output.coordinator.up = some d) :
    ∃ ledger,
      ReferenceCoordinatorUpPhysicalCall.siteLedger? (x := record.input) = some ledger ∧
      CoordinatorUpReception.receptionInputCheck
        (ReferenceCoordinatorUpPhysicalCall.actualUpInput record.input ledger) = true ∧
      d.input = ReferenceCoordinatorUpPhysicalCall.actualUpInput record.input ledger ∧
      d.decoderAfter = (CoordinatorUpReception.decoderTransition
        (ReferenceCoordinatorUpPhysicalCall.actualUpInput record.input ledger)).1 ∧
      d.raw = (CoordinatorUpReception.decoderTransition
        (ReferenceCoordinatorUpPhysicalCall.actualUpInput record.input ledger)).2 := by
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
            obtain ⟨ledgerStarted, hsite, hcheck, hinput, hafter, hraw⟩ :=
              collectionPostChoice_up_raw x registers.payload
                (ReferenceActivePhysicalStep.sharedLedger ledger) dispatched.startResult
                (ReferenceActivePhysicalStep.liveRegistersAt registers x.time).complementWeights
                d hdiagnostic
            refine ⟨ledgerStarted, ?_, hcheck, hinput, hafter, hraw⟩
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
            obtain ⟨ledgerStarted, hsite, hcheck, hinput, hafter, hraw⟩ :=
              collectionPostChoice_up_raw x payload ledger snapshot.clockStarted
                (CoordinatorCollectionInteractive.PreObservationInputs.weights source
                  snapshot.inputsValid.ledger_valid snapshot.inputsValid.assignment_eq)
                d hdiagnostic
            refine ⟨ledgerStarted, ?_, hcheck, hinput, hafter, hraw⟩
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

private theorem decoder_run_append (trace : AffineBatchDecoder.Trace p)
    (left right : List (Fin p.T))
    (state : AffineBatchDecoder.State p.T (AffineBatchDecoder.width p)) :
    AffineBatchDecoder.run p trace (left ++ right) state =
      AffineBatchDecoder.run p trace right (AffineBatchDecoder.run p trace left state) := by
  induction left generalizing state with
  | nil => rfl
  | cons time left ih =>
      calc
        AffineBatchDecoder.run p trace ((time :: left) ++ right) state =
            AffineBatchDecoder.run p trace (left ++ right)
              (AffineBatchDecoder.step p trace state time) := rfl
        _ = AffineBatchDecoder.run p trace right
              (AffineBatchDecoder.run p trace left
                (AffineBatchDecoder.step p trace state time)) := ih _
        _ = AffineBatchDecoder.run p trace right
              (AffineBatchDecoder.run p trace (time :: left) state) := by
            rw [AffineBatchDecoder.run]

private theorem decoder_run_congr_on_rounds (left right : AffineBatchDecoder.Trace p)
    (rounds : List (Fin p.T))
    (state : AffineBatchDecoder.State p.T (AffineBatchDecoder.width p))
    (htrace : ∀ time, time ∈ rounds → left time = right time) :
    AffineBatchDecoder.run p left rounds state =
      AffineBatchDecoder.run p right rounds state := by
  induction rounds generalizing state with
  | nil => rfl
  | cons time rounds ih =>
      have htime := htrace time (by simp)
      have htail : ∀ current, current ∈ rounds → left current = right current := by
        intro current hcurrent
        exact htrace current (by simp [hcurrent])
      simp only [AffineBatchDecoder.run]
      have hpositive : AffineBatchDecoder.positiveAt p left time =
          AffineBatchDecoder.positiveAt p right time := by
        simp [AffineBatchDecoder.positiveAt, AffineBatchDecoder.entry, htime]
      rw [show AffineBatchDecoder.step p left state time =
          AffineBatchDecoder.step p right state time by
        simp [AffineBatchDecoder.step, hpositive]]
      exact ih _ htail

private theorem decoder_run_ineligible_suffix (trace : AffineBatchDecoder.Trace p)
    (suffix : List (Fin p.T))
    (state : AffineBatchDecoder.State p.T (AffineBatchDecoder.width p))
    (hsmall : state.pending.length < AffineBatchDecoder.quota p)
    (hineligible : ∀ time, time ∈ suffix → ¬ AffineBatchDecoder.eligible (trace time)) :
    AffineBatchDecoder.run p trace suffix state = state := by
  induction suffix generalizing state with
  | nil => rfl
  | cons time suffix ih =>
      have hstep := AffineBatchDecoder.step_ineligible p trace state time hsmall
        (hineligible time (by simp))
      calc
        AffineBatchDecoder.run p trace (time :: suffix) state =
            AffineBatchDecoder.run p trace suffix (AffineBatchDecoder.step p trace state time) := rfl
        _ = AffineBatchDecoder.run p trace suffix state := by rw [hstep]
        _ = state := ih state hsmall (by
          intro current hcurrent
          exact hineligible current (by simp [hcurrent]))

/-- Link the interval's actual second positive window to the retained
diagnostic at its located physical call. The pre-call bank is replayed from the
same actual interval prefix. The transition clears and appends the exact tested
window even when its raw solver output is `none`; no decoder success, message
truth, filter agreement, or acceptance is assumed.
-/
theorem run_interval_saved_completed_cut
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start a b : ℕ) (hab : a ≤ b) (hspan : start + b ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hinitial : ReferenceUpDecoderBankInvariant.upBankInvariant initial)
    (hordinary : (ReferenceActivePhysicalHorizon.run initial rows selected rewards start b
      hspan hmode).finalState.coordinator ≠ .dagger)
    (i : Fin (p.m - 1))
    (hseed : AffineBatchDecoder.collected (initial.upDecoderBank i) = [])
    (hpositiveCount :
      (AffineBatchDecoder.positives p
        (ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace
          (ReferenceCoordinatorUpIntervalWindow.intervalRecords
            initial rows selected rewards start a b hspan hmode) i)
        (ReferenceCoordinatorUpIntervalWindow.intervalRounds
          initial rows selected rewards start a b hspan hmode)).length =
      AffineBatchDecoder.quota p -
        ((ReferenceActivePhysicalHorizon.run initial rows selected rewards start a
          (by omega) hmode).finalState.upDecoderBank i).pending.length +
          AffineBatchDecoder.quota p) :
    let preRun := ReferenceActivePhysicalHorizon.run initial rows selected rewards start a
      (by omega) hmode
    let full := ReferenceActivePhysicalHorizon.run initial rows selected rewards start b
      hspan hmode
    let interval := full.records.drop a
    let trace := ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace interval i
    let rounds := ReferenceCoordinatorUpIntervalWindow.intervalRounds
      initial rows selected rewards start a b hspan hmode
    let positive := AffineBatchDecoder.positives p trace rounds
    let channel := preRun.finalState.upDecoderBank i
    let window := positive.drop (AffineBatchDecoder.quota p - channel.pending.length)
    ∃ (first : List (AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p)))
      (last : AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p))
      (index : Fin rounds.length)
      (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
      (diagnostic : ReferenceActivePhysicalStep.UpDiagnostic p rate),
      let before := AffineBatchDecoder.run p trace (rounds.take index.val) channel
      first = channel.pending ++ positive.take
          (AffineBatchDecoder.quota p - channel.pending.length) ∧
      first.length = AffineBatchDecoder.quota p ∧
      window.length = AffineBatchDecoder.quota p ∧
      window.Pairwise (fun earlier later => earlier.time.val < later.time.val) ∧
      last ∈ window ∧
      AffineBatchDecoder.decisionTime window = some last.time ∧
      rounds.get index = last.time ∧
      record ∈ interval ∧
      record.input.time = last.time ∧
      record.output.coordinator.up = some diagnostic ∧
      diagnostic.input.selectedFollower = i ∧
      diagnostic.input.time = record.input.time ∧
      last = AffineBatchDecoder.entry p trace last.time ∧
      last.sample = ((record.input.rows record.input.selected).2 record.input.time).2
        (1, CoordinatorUpMeasurability.selectedChannelFollower
          ((record.input.rows record.input.selected).2 record.input.time)) ∧
      (∃ ledger,
        ReferenceCoordinatorUpPhysicalCall.siteLedger? (x := record.input) = some ledger ∧
        CoordinatorUpReception.receptionInputCheck
          (ReferenceCoordinatorUpPhysicalCall.actualUpInput record.input ledger) = true ∧
        diagnostic.input = ReferenceCoordinatorUpPhysicalCall.actualUpInput record.input ledger ∧
        diagnostic.decoderAfter = (CoordinatorUpReception.decoderTransition
          (ReferenceCoordinatorUpPhysicalCall.actualUpInput record.input ledger)).1 ∧
        diagnostic.input.time = record.input.time ∧
        diagnostic.input.selectedFollower =
          CoordinatorUpMeasurability.selectedFollowerIndex
            ((record.input.rows record.input.selected).2 record.input.time) ∧
        diagnostic.input.affineSample =
          ((record.input.rows record.input.selected).2 record.input.time).2
            (1, CoordinatorUpMeasurability.selectedChannelFollower
              ((record.input.rows record.input.selected).2 record.input.time)) ∧
        diagnostic.input.ownObservation =
          (ReferenceActivePhysicalStep.prepare record.input).feedback.feedback
            (ActiveRoundActions.coordinator p.two_le_m) ∧
        (ReferenceActivePhysicalStep.prepare record.input).feedback.feedback
            (ActiveRoundActions.coordinator p.two_le_m) =
          (if FiniteBanditModel.collisionFreeFor
              (ReferenceActivePhysicalStep.prepare record.input).arms.actions
                (ActiveRoundActions.coordinator p.two_le_m) then
            record.input.rewards record.input.time
              ((ReferenceActivePhysicalStep.prepare record.input).arms.actions
                (ActiveRoundActions.coordinator p.two_le_m))
          else 0) ∧
        (ReferenceCoordinatorUpDecoderReplay.retainedUpRoundInput diagnostic).receiverEnabled = true ∧
        (ReferenceCoordinatorUpDecoderReplay.retainedUpRoundInput diagnostic).sample =
          diagnostic.input.affineSample ∧
        (ReferenceCoordinatorUpDecoderReplay.retainedUpRoundInput diagnostic).roundedReward =
          CoordinatorUpReception.roundedObservationValue p diagnostic.input.ownObservation ∧
        (AffineBatchDecoder.eligible
          (ReferenceCoordinatorUpDecoderReplay.retainedUpRoundInput diagnostic) ↔
          CoordinatorUpReception.receptionGate diagnostic.input ∧
            0 < CoordinatorUpReception.roundedObservationValue p
              diagnostic.input.ownObservation) ∧
        record.output.ownEntries (ActiveRoundActions.coordinator p.two_le_m) =
          (record.output.preparation.arms.actions
            (ActiveRoundActions.coordinator p.two_le_m),
            ActualInitializationPhysicalStep.observationOfGrid p
              (record.output.preparation.feedback.feedback
                (ActiveRoundActions.coordinator p.two_le_m)))) ∧
      ReferenceActivePhysicalHorizon.Connected preRun.finalState
        (interval.take index.val) record.input.state ∧
      record.input.state.upDecoderBank =
        ReferenceCoordinatorUpDecoderReplay.replay preRun.finalState.upDecoderBank
          (ReferenceCoordinatorUpDecoderReplay.retainedUpDiagnostics
            (interval.take index.val)) ∧
      diagnostic.input.upDecoderBank = record.input.state.upDecoderBank ∧
      before = diagnostic.input.upDecoderBank i ∧
      before.pending ++ [AffineBatchDecoder.entry p trace last.time] = window ∧
      (CoordinatorUpReception.decoderTransition diagnostic.input).1.pending = [] ∧
      (CoordinatorUpReception.decoderTransition diagnostic.input).1.completed =
        channel.completed ++ [first, window] ∧
      diagnostic.decoderAfter = (CoordinatorUpReception.decoderTransition diagnostic.input).1 ∧
      diagnostic.raw = (CoordinatorUpReception.decoderTransition diagnostic.input).2 ∧
      diagnostic.raw = AffineBatchDecoder.batchOutput window ∧
      CoordinatorUpReception.decoderTransition diagnostic.input =
        (⟨[], channel.completed ++ [first, window]⟩,
          AffineBatchDecoder.batchOutput window) ∧
      AffineBatchDecoder.run p trace rounds channel =
        ⟨[], channel.completed ++ [first, window]⟩ ∧
      AffineBatchDecoder.run p trace rounds channel = full.finalState.upDecoderBank i := by
  classical
  let preRun := ReferenceActivePhysicalHorizon.run initial rows selected rewards start a
    (by omega) hmode
  let full := ReferenceActivePhysicalHorizon.run initial rows selected rewards start b hspan hmode
  let interval := full.records.drop a
  let trace := ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace interval i
  let rounds := ReferenceCoordinatorUpIntervalWindow.intervalRounds
    initial rows selected rewards start a b hspan hmode
  let positive := AffineBatchDecoder.positives p trace rounds
  let channel := preRun.finalState.upDecoderBank i
  let window := positive.drop (AffineBatchDecoder.quota p - channel.pending.length)
  have hgeometry := ReferenceCoordinatorUpIntervalWindow.run_interval_two_batch_window
    initial rows selected rewards start a b hab hspan hmode hinitial hordinary i hseed
    hpositiveCount
  obtain ⟨first, last, index, hrun, hfull, hfirst, hfirstLen, hwindowLen,
    hwindowChronological, hpendingDisjoint, hcountBound, hwindowBounds, hlastWindow,
    hdecision, hindexRound, hlastEligible, hlastSample, hwindowMax, hrawWindow⟩ := hgeometry
  have hcut := ReferenceCoordinatorUpIntervalWindow.run_interval_cut initial rows selected
    rewards start a b hab hspan hmode hinitial hordinary
  rcases hcut with ⟨hprefixRecords, hdecomp, hintervalConnected, hpreInvariant,
    hpreOrdinary, hrecordInvariant, hrecordSuccessorOrdinary⟩
  have hroundsChronological :=
    ReferenceCoordinatorUpIntervalWindow.run_interval_rounds_chronological
      initial rows selected rewards start a b hab hspan hmode hinitial hordinary
  have hintervalChronological : interval.Pairwise
      (fun earlier later => earlier.input.time.val < later.input.time.val) := by
    have hroundValues : (rounds.map Fin.val).Pairwise LT.lt :=
      List.pairwise_map.mpr hroundsChronological
    have hvalues : (interval.map (fun current => current.input.time.val)).Pairwise LT.lt := by
      simpa [rounds, ReferenceCoordinatorUpIntervalWindow.intervalRounds,
        interval, full, ReferenceCoordinatorUpIntervalWindow.intervalRecords,
        List.map_map, Function.comp_def] using hroundValues
    exact List.pairwise_map.mp hvalues
  have hindexInterval : index.val < interval.length := by
    simpa [rounds, ReferenceCoordinatorUpIntervalWindow.intervalRounds,
      interval, full, ReferenceCoordinatorUpIntervalWindow.intervalRecords] using index.isLt
  let record := interval.get ⟨index.val, hindexInterval⟩
  have hrecordMem : record ∈ interval := by
    dsimp [record]
    exact List.getElem_mem _
  have hindexRoundElem : rounds[index.val]'index.isLt = last.time := by
    simpa only [List.get_eq_getElem] using hindexRound
  have hmapElem : (interval.map (fun current => current.input.time))[index.val]'
      (by simpa using hindexInterval) =
      last.time := by
    simpa [rounds, ReferenceCoordinatorUpIntervalWindow.intervalRounds,
      interval, full, ReferenceCoordinatorUpIntervalWindow.intervalRecords] using hindexRoundElem
  have hrecordTime : record.input.time = last.time := by
    simpa [record, interval, full] using hmapElem
  have htraceRecord :=
    ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace_at_record
      interval i hintervalChronological record hrecordMem
  have hdiagnostic : ∃ diagnostic,
      record.output.coordinator.up = some diagnostic ∧
        diagnostic.input.selectedFollower = i := by
    cases hcall : record.output.coordinator.up with
    | none =>
        have hineligible : ¬ AffineBatchDecoder.eligible (trace last.time) := by
          change ¬ AffineBatchDecoder.eligible
            (ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace interval i last.time)
          rw [← hrecordTime, htraceRecord]
          simp [ReferenceCoordinatorUpIntervalWindow.recordFocalInput,
            hcall,
            ReferenceCoordinatorUpIntervalWindow.administrativeNoCallInput,
            AffineBatchDecoder.eligible]
        exact False.elim (hineligible hlastEligible)
    | some diagnostic =>
        by_cases hselected : diagnostic.input.selectedFollower = i
        · exact ⟨diagnostic, rfl, hselected⟩
        · have hineligible : ¬ AffineBatchDecoder.eligible (trace last.time) := by
            change ¬ AffineBatchDecoder.eligible
              (ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace interval i last.time)
            rw [← hrecordTime, htraceRecord]
            simp [ReferenceCoordinatorUpIntervalWindow.recordFocalInput,
              hcall,
              ReferenceCoordinatorUpDecoderReplay.retainedUpRoundInput,
              hselected, AffineBatchDecoder.eligible]
          exact False.elim (hineligible hlastEligible)
  obtain ⟨diagnostic, hdiagnostic, hselected⟩ := hdiagnostic
  have hphysical := ReferenceCoordinatorUpIntervalWindow.record_retained_up_actual_call
    record diagnostic hdiagnostic
  have hphysicalKeep := hphysical
  rcases hphysical with ⟨ledger, hsite, _, hinput, hdecoderAfterPhysical,
    hdiagnosticTime, _, horiginalSample,
    _, _, _, _, _, _, _⟩
  have htransitionLinks := record_retained_up_transition record diagnostic hdiagnostic
  rcases htransitionLinks with ⟨ledgerRaw, hsiteRaw, _, hinputRaw, _, hrawSaved⟩
  have hledgerEq : ledgerRaw = ledger := Option.some.inj (hsiteRaw.symm.trans hsite)
  rw [hledgerEq] at hinputRaw hrawSaved
  have hdecoderAfter : diagnostic.decoderAfter =
      (CoordinatorUpReception.decoderTransition diagnostic.input).1 := by
    rw [← hinput] at hdecoderAfterPhysical
    exact hdecoderAfterPhysical
  have hrawSavedDiagnostic : diagnostic.raw =
      (CoordinatorUpReception.decoderTransition diagnostic.input).2 := by
    rw [← hinput] at hrawSaved
    exact hrawSaved
  obtain ⟨_, _, _, hbank, _, _, _, _, _, _, _, _, _⟩ :=
    ReferenceCoordinatorUpPhysicalCall.record_retained_up_input_fields
      record diagnostic hdiagnostic
  have hdiagnosticTimeLast : diagnostic.input.time = last.time :=
    hdiagnosticTime.trans hrecordTime
  have htraceActual : trace last.time = CoordinatorUpReception.roundInput diagnostic.input := by
    calc
      trace last.time = trace record.input.time := by rw [hrecordTime.symm]
      _ = ReferenceCoordinatorUpIntervalWindow.recordFocalInput record i := htraceRecord
      _ = ReferenceCoordinatorUpDecoderReplay.retainedUpRoundInput diagnostic := by
        simp [ReferenceCoordinatorUpIntervalWindow.recordFocalInput, hdiagnostic, hselected]
      _ = CoordinatorUpReception.roundInput diagnostic.input := rfl
  have hlastSampleOriginal : last.sample =
      ((record.input.rows record.input.selected).2 record.input.time).2
        (1, CoordinatorUpMeasurability.selectedChannelFollower
          ((record.input.rows record.input.selected).2 record.input.time)) := by
    have hsampleCall : (trace last.time).sample =
        ((record.input.rows record.input.selected).2 record.input.time).2
          (1, CoordinatorUpMeasurability.selectedChannelFollower
            ((record.input.rows record.input.selected).2 record.input.time)) := by
      exact (congrArg AffineBatchDecoder.RoundInput.sample htraceActual).trans
        (by simpa [CoordinatorUpReception.roundInput] using horiginalSample)
    exact hlastSample.trans hsampleCall
  have hlastEntry : last = AffineBatchDecoder.entry p trace last.time := by
    cases last with
    | mk time sample =>
        simpa [AffineBatchDecoder.entry] using hlastSample
  have hprefix : interval = interval.take index.val ++ [record] ++
      interval.drop (index.val + 1) := by
    have htake : interval.take (index.val + 1) =
        interval.take index.val ++ [record] := by
      simp [record, List.get_eq_getElem]
    calc
      interval = interval.take (index.val + 1) ++ interval.drop (index.val + 1) :=
        (List.take_append_drop (index.val + 1) interval).symm
      _ = (interval.take index.val ++ [record]) ++ interval.drop (index.val + 1) := by
        rw [htake]
      _ = interval.take index.val ++ [record] ++ interval.drop (index.val + 1) := by
        rw [List.append_assoc]
  have hsplitConnected : ReferenceActivePhysicalHorizon.Connected preRun.finalState
      (interval.take index.val ++ (record :: interval.drop (index.val + 1))) full.finalState := by
    have hprefix' : interval = interval.take index.val ++
        (record :: interval.drop (index.val + 1)) := by
      simpa [List.cons_append, List.append_assoc] using hprefix
    rw [← hprefix']
    exact hintervalConnected
  obtain ⟨middle, hprefixConnected, hrecordAndSuffix⟩ :=
    connected_append_split (interval.take index.val)
      (record :: interval.drop (index.val + 1)) hsplitConnected
  have hrecordAndSuffixParts : record.input.state = middle ∧
      ReferenceActivePhysicalHorizon.Connected record.output.next
        (interval.drop (index.val + 1)) full.finalState := by
    simpa [ReferenceActivePhysicalHorizon.Connected] using hrecordAndSuffix
  have hprefixConnectedActual : ReferenceActivePhysicalHorizon.Connected preRun.finalState
      (interval.take index.val) record.input.state := by
    rw [hrecordAndSuffixParts.1]
    exact hprefixConnected
  have hrecordStateConnected : ReferenceActivePhysicalHorizon.Connected record.input.state
      (record :: interval.drop (index.val + 1)) full.finalState :=
    ⟨rfl, hrecordAndSuffixParts.2⟩
  have hrecordStateOrdinary : record.input.state.coordinator ≠ .dagger := by
    intro hdagger
    exact hordinary
      (ReferenceActivePhysicalHorizon.Connected.coordinator_dagger
        hrecordStateConnected hdagger).1
  have hprefixInvariant : ∀ current, current ∈ interval.take index.val →
      ReferenceUpDecoderBankInvariant.upBankInvariant current.input.state := by
    intro current hcurrent
    have hcurrentInterval := mem_of_mem_take_list interval index.val hcurrent
    have hcurrentFull : current ∈ full.records := by
      have hcurrent' := mem_of_mem_drop_list full.records a hcurrentInterval
      simpa [interval] using hcurrent'
    exact hrecordInvariant current (by simpa [full] using hcurrentFull)
  have hprefixBank := connected_prefix_upDecoderBank_replay hprefixConnectedActual
    hprefixInvariant hrecordStateOrdinary
  have hprefixChronological : (interval.take index.val).Pairwise
      (fun earlier later => earlier.input.time.val < later.input.time.val) := by
    apply List.Pairwise.sublist (List.take_sublist _ _)
    exact hintervalChronological
  have hpreBankWellFormed : CoordinatorUpReception.decoderBankWellFormed p
      preRun.finalState.upDecoderBank := hpreInvariant.1
  have hfoldPrefix := ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace_run_eq_replay
    (interval.take index.val) i hprefixChronological preRun.finalState.upDecoderBank
    (hpreBankWellFormed i)
  have hroundPrefix : rounds.take index.val =
      (interval.take index.val).map (fun current => current.input.time) := by
    simp [rounds, ReferenceCoordinatorUpIntervalWindow.intervalRounds,
      interval, full, ReferenceCoordinatorUpIntervalWindow.intervalRecords]
  have hprefixTrace : ∀ current, current ∈ interval.take index.val →
      ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace interval i current.input.time =
        ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace
          (interval.take index.val) i current.input.time := by
    intro current hcurrent
    have hwhole := ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace_at_record
      interval i hintervalChronological current
      (mem_of_mem_take_list interval index.val hcurrent)
    have hprefix := ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace_at_record
      (interval.take index.val) i hprefixChronological current hcurrent
    exact hwhole.trans hprefix.symm
  have hprefixTraceRounds : ∀ time, time ∈
      (interval.take index.val).map (fun current => current.input.time) →
      trace time = ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace
        (interval.take index.val) i time := by
    intro time htime
    rcases List.mem_map.mp htime with ⟨current, hcurrent, htimeEq⟩
    subst time
    exact hprefixTrace current hcurrent
  have hprefixRunCongr := decoder_run_congr_on_rounds trace
    (ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace (interval.take index.val) i)
    ((interval.take index.val).map (fun current => current.input.time))
    (preRun.finalState.upDecoderBank i) hprefixTraceRounds
  have hbeforeBank : AffineBatchDecoder.run p trace (rounds.take index.val) channel =
      record.input.state.upDecoderBank i := by
    calc
      _ = AffineBatchDecoder.run p trace
          ((interval.take index.val).map (fun current => current.input.time))
          (preRun.finalState.upDecoderBank i) := by rw [hroundPrefix]
      _ = AffineBatchDecoder.run p
          (ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace (interval.take index.val) i)
          ((interval.take index.val).map (fun current => current.input.time))
          (preRun.finalState.upDecoderBank i) := hprefixRunCongr
      _ = (ReferenceCoordinatorUpDecoderReplay.replay preRun.finalState.upDecoderBank
          (ReferenceCoordinatorUpDecoderReplay.retainedUpDiagnostics
            (interval.take index.val))) i := hfoldPrefix
      _ = record.input.state.upDecoderBank i := congrArg (fun bank => bank i) hprefixBank.symm
  have hdiagnosticBank : diagnostic.input.upDecoderBank = record.input.state.upDecoderBank := hbank
  have hbeforeDiagnostic :
      AffineBatchDecoder.run p trace (rounds.take index.val) channel =
        diagnostic.input.upDecoderBank i := by
    rw [hdiagnosticBank]
    exact hbeforeBank
  let before := AffineBatchDecoder.run p trace (rounds.take index.val) channel
  let suffix := rounds.drop (index.val + 1)
  have hroundsSplit : rounds = rounds.take index.val ++ [last.time] ++ suffix := by
    have htake : rounds.take (index.val + 1) = rounds.take index.val ++ [rounds.get index] :=
      (List.take_append_getElem index.isLt).symm
    calc
      rounds = rounds.take (index.val + 1) ++ rounds.drop (index.val + 1) :=
        (List.take_append_drop (index.val + 1) rounds).symm
      _ = (rounds.take index.val ++ [rounds.get index]) ++ suffix := by rw [htake]
      _ = rounds.take index.val ++ [last.time] ++ suffix := by rw [hindexRound]
  have hpositivePairwise : positive.Pairwise
      (fun earlier later => earlier.time.val < later.time.val) := by
    change (((rounds.filter (fun time => decide (AffineBatchDecoder.eligible (trace time)))).map
      (AffineBatchDecoder.entry p trace)).Pairwise
        (fun earlier later => earlier.time.val < later.time.val))
    apply List.pairwise_map.mpr
    simpa only [AffineBatchDecoder.entry, AffineBatchDecoder.Entry.time] using
      hroundsChronological.filter _
  have hpositiveSplit : positive = positive.take
      (AffineBatchDecoder.quota p - channel.pending.length) ++ window := by
    dsimp [window]
    exact (List.take_append_drop _ _).symm
  have hwindowNonempty : window ≠ [] := by
    intro hempty
    have hquota := AffineBatchDecoder.quota_pos p
    have hlength : window.length = AffineBatchDecoder.quota p := hwindowLen
    have hzero : window.length = 0 := by simp [hempty]
    omega
  have hlastInDrop : last ∈ positive.drop
      (AffineBatchDecoder.quota p - channel.pending.length) := by
    simpa [window] using hlastWindow
  have htakeDropPairwise :
      (positive.take (AffineBatchDecoder.quota p - channel.pending.length) ++
        positive.drop (AffineBatchDecoder.quota p - channel.pending.length)).Pairwise
          (fun earlier later => earlier.time.val < later.time.val) := by
    rw [List.take_append_drop]
    exact hpositivePairwise
  have hcross := (List.pairwise_append.mp htakeDropPairwise).2.2
  have hnoPositiveSuffix : ∀ time, time ∈ suffix →
      ¬ AffineBatchDecoder.eligible (trace time) := by
    intro time htime heligible
    obtain ⟨suffixIndex, hsuffixIndex, hsuffixGet⟩ :=
      (List.exists_mem_iff_getElem).mp ⟨time, htime, rfl⟩
    have hglobalBound : index.val + 1 + suffixIndex < rounds.length := by
      have hlength := hsuffixIndex
      simp [suffix, List.length_drop] at hlength
      omega
    have hglobalGet : rounds[index.val + 1 + suffixIndex]'hglobalBound = time := by
      simpa [suffix, List.getElem_drop] using hsuffixGet.symm
    have htimeAfter : last.time.val < time.val := by
      have hlt : index < ⟨index.val + 1 + suffixIndex, hglobalBound⟩ :=
        Fin.mk_lt_mk.mpr (by omega)
      have hpair := hroundsChronological.rel_get_of_lt hlt
      have hglobalFin : rounds.get ⟨index.val + 1 + suffixIndex, hglobalBound⟩ = time := by
        simpa only [List.get_eq_getElem] using hglobalGet
      rw [hindexRound, hglobalFin] at hpair
      exact hpair
    have hpositiveEntry : AffineBatchDecoder.entry p trace time ∈ positive := by
      apply List.mem_map.mpr
      refine ⟨time, List.mem_filter.mpr ⟨
        mem_of_mem_drop_list rounds (index.val + 1) htime, ?_⟩, rfl⟩
      exact decide_eq_true heligible
    rw [hpositiveSplit] at hpositiveEntry
    rcases List.mem_append.mp hpositiveEntry with hfirstWindow | hsecondWindow
    · have hbeforeLast := hcross _ hfirstWindow last hlastInDrop
      have hafterLast := htimeAfter
      simp only [AffineBatchDecoder.entry] at hbeforeLast hafterLast
      omega
    · have hwindowEntry : AffineBatchDecoder.entry p trace time ∈ window := by
        simpa [window] using hsecondWindow
      have hmax := hwindowMax _ hwindowEntry
      have hmaxTime : time.val ≤ last.time.val := by
        simpa [AffineBatchDecoder.entry] using hmax
      omega
  have hbeforePendingSmall : before.pending.length < AffineBatchDecoder.quota p := by
    have hspec := AffineBatchDecoder.run_spec p trace (rounds.take index.val) channel
      (hpreBankWellFormed i).1 (hpreBankWellFormed i).2
    exact hspec.1
  have hstepSpec := AffineBatchDecoder.step_spec p trace before last.time
    hbeforePendingSmall
    (AffineBatchDecoder.run_spec p trace (rounds.take index.val) channel
      (hpreBankWellFormed i).1 (hpreBankWellFormed i).2).2.1
  have hsuffixNoop := decoder_run_ineligible_suffix trace suffix
    (AffineBatchDecoder.step p trace before last.time) hstepSpec.1 hnoPositiveSuffix
  have hstepFinal : AffineBatchDecoder.step p trace before last.time =
      ⟨[], channel.completed ++ [first, window]⟩ := by
    calc
      _ = AffineBatchDecoder.run p trace suffix
          (AffineBatchDecoder.step p trace before last.time) := hsuffixNoop.symm
      _ = AffineBatchDecoder.run p trace rounds channel := by
        calc
          _ = AffineBatchDecoder.run p trace ([last.time] ++ suffix) before := by
            calc
              _ = AffineBatchDecoder.run p trace suffix
                  (AffineBatchDecoder.run p trace [last.time] before) :=
                (decoder_run_append trace [last.time] suffix before).symm
              _ = _ := rfl
          _ = AffineBatchDecoder.run p trace (rounds.take index.val ++ [last.time] ++ suffix)
              channel := by
            simpa [List.append_assoc] using
              (decoder_run_append trace (rounds.take index.val) ([last.time] ++ suffix) channel).symm
          _ = AffineBatchDecoder.run p trace rounds channel := by
            congr 1
            exact hroundsSplit.symm
      _ = _ := hrun
  have hpositiveAt : AffineBatchDecoder.positiveAt p trace last.time =
      [AffineBatchDecoder.entry p trace last.time] := by
    unfold AffineBatchDecoder.positiveAt
    rw [ite_eq_left hlastEligible]
  have happendedNonempty :
      before.pending ++ AffineBatchDecoder.positiveAt p trace last.time ≠ [] := by
    rw [hpositiveAt]
    simp
  have hcompletedBranch :
      ¬ (before.pending ++ AffineBatchDecoder.positiveAt p trace last.time).length <
        AffineBatchDecoder.quota p := by
    intro hsmall
    have hstatePending :
        (AffineBatchDecoder.step p trace before last.time).pending =
          before.pending ++ AffineBatchDecoder.positiveAt p trace last.time := by
      have hsmall' : before.pending.length +
          (AffineBatchDecoder.positiveAt p trace last.time).length <
            AffineBatchDecoder.quota p := by
        simpa only [List.length_append] using hsmall
      simp [AffineBatchDecoder.step, hsmall']
    rw [hstepFinal] at hstatePending
    change ([] : List (AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p))) =
      before.pending ++ AffineBatchDecoder.positiveAt p trace last.time at hstatePending
    exact happendedNonempty hstatePending.symm
  have hcompletedBranch' :
      ¬ before.pending.length + (AffineBatchDecoder.positiveAt p trace last.time).length <
        AffineBatchDecoder.quota p := by
    simpa only [List.length_append] using hcompletedBranch
  have hcompletedList :
      before.completed ++
        [before.pending ++ AffineBatchDecoder.positiveAt p trace last.time] =
          channel.completed ++ [first, window] := by
    have h := congrArg AffineBatchDecoder.State.completed hstepFinal
    simp only [AffineBatchDecoder.step, List.length_append] at h
    rw [ite_eq_right hcompletedBranch'] at h
    exact h
  have htested :
      before.pending ++ [AffineBatchDecoder.entry p trace last.time] = window := by
    have hlastLeft :
        (before.completed ++
          [before.pending ++ AffineBatchDecoder.positiveAt p trace last.time]).getLast? =
            some (before.pending ++ AffineBatchDecoder.positiveAt p trace last.time) := by
      simp
    have hlastRight : (channel.completed ++ [first, window]).getLast? = some window := by
      simp
    have hlastEq := congrArg List.getLast? hcompletedList
    rw [hlastLeft, hlastRight] at hlastEq
    have hbatch := Option.some.inj hlastEq
    rw [hpositiveAt] at hbatch
    exact hbatch
  have hdecodeState : (AffineBatchDecoder.decodeStep p trace before last.time).1 =
      ⟨[], channel.completed ++ [first, window]⟩ := by
    simpa [AffineBatchDecoder.decodeStep] using hstepFinal
  have hdecodeRaw : (AffineBatchDecoder.decodeStep p trace before last.time).2 =
      AffineBatchDecoder.batchOutput window := hrawWindow
  have hdecodePair : AffineBatchDecoder.decodeStep p trace before last.time =
      (⟨[], channel.completed ++ [first, window]⟩,
        AffineBatchDecoder.batchOutput window) := by
    exact Prod.ext hdecodeState hdecodeRaw
  have htransition : CoordinatorUpReception.decoderTransition diagnostic.input =
      (⟨[], channel.completed ++ [first, window]⟩,
        AffineBatchDecoder.batchOutput window) := by
    have hstate : diagnostic.input.upDecoderBank diagnostic.input.selectedFollower = before := by
      calc
        diagnostic.input.upDecoderBank diagnostic.input.selectedFollower =
            diagnostic.input.upDecoderBank i := by rw [hselected]
        _ = record.input.state.upDecoderBank i := congrArg (fun bank => bank i) hbank
        _ = before := hbeforeBank.symm
    have hcurrent := ReferenceCoordinatorUpDecoderReplay.decodeStep_constantInput_of_current_eq
      trace before last.time diagnostic.input htraceActual
    calc
      _ = AffineBatchDecoder.decodeStep p (CoordinatorUpReception.traceAt diagnostic.input)
          (diagnostic.input.upDecoderBank diagnostic.input.selectedFollower)
          diagnostic.input.time := rfl
      _ = AffineBatchDecoder.decodeStep p (CoordinatorUpReception.traceAt diagnostic.input)
          before last.time := by rw [hstate, hdiagnosticTimeLast]
      _ = AffineBatchDecoder.decodeStep p
          (ReferenceCoordinatorUpDecoderReplay.constantInputTrace diagnostic.input)
          before last.time := by rfl
      _ = AffineBatchDecoder.decodeStep p trace before last.time := hcurrent.symm
      _ = _ := hdecodePair
  have hsavedRaw : diagnostic.raw = AffineBatchDecoder.batchOutput window := by
    rw [hrawSavedDiagnostic, htransition]
  have htransitionState := congrArg Prod.fst htransition
  have htransitionRaw := congrArg Prod.snd htransition
  refine ⟨first, last, index, record, diagnostic, ?_⟩
  dsimp only [before]
  refine ⟨hfirst, hfirstLen, hwindowLen, hwindowChronological, hlastWindow,
    hdecision, hindexRound, hrecordMem, hrecordTime, hdiagnostic, hselected,
    hdiagnosticTime, hlastEntry, hlastSampleOriginal, hphysicalKeep,
    hprefixConnectedActual, hprefixBank, hdiagnosticBank, hbeforeDiagnostic,
    htested, ?_, ?_, hdecoderAfter, hrawSavedDiagnostic, hsavedRaw, htransition,
    hrun, hfull⟩
  · simpa only [Prod.fst] using congrArg AffineBatchDecoder.State.pending htransitionState
  · simpa only [Prod.fst] using congrArg AffineBatchDecoder.State.completed htransitionState

end Bandits.Support.ReferenceCoordinatorUpWindowCompletedCut

end
