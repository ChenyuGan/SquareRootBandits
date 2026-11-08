/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceUpDecoderBankInvariant

import Mathlib.Data.List.Basic

/-!
# Replay of retained physical coordinator UP-decoder calls

Sources: `sources/zip4/manuscript/05_binary_transport.tex:36-48,70-124`,
`sources/zip4/manuscript/06_interruptions.tex:277-284,327-348`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:92-109,131-138`.

This module defines replay from the actual `H.run` record diagnostics. Its
trace extension is constant at a retained receiver's literal round input; the
decoder consumes only that current input. A replay step uses its accumulator
as decoder state. The diagnostic's bank and decoder-after fields are kept as
observations to be identified with the physical prefix, never as replay state.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.CoordinatorUpReception
open Bandits.Support.AffineBatchDecoder
open Bandits.Support.ReferenceUpDecoderBankInvariant

namespace Bandits.Support.ReferenceCoordinatorUpDecoderReplay

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput

variable {p : Parameters} {rate : RateInput p}
/-- The only retained diagnostic projection used as the UP-call calendar. -/
def retainedUpDiagnostics
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))) :
    List (ReferenceActivePhysicalStep.UpDiagnostic p rate) :=
  records.filterMap (fun record => record.output.coordinator.up)
/-- Literal selected channel recorded by an actual coordinator UP diagnostic. -/
def retainedUpFollower
    (diagnostic : ReferenceActivePhysicalStep.UpDiagnostic p rate) : Fin (p.m - 1) :=
  diagnostic.input.selectedFollower
/-- Literal physical coordinate recorded by an actual coordinator UP diagnostic. -/
def retainedUpTime
    (diagnostic : ReferenceActivePhysicalStep.UpDiagnostic p rate) : Fin p.T :=
  diagnostic.input.time
/-- Preserve the complete four-field receiver input saved by the actual call. -/
def retainedUpRoundInput
    (diagnostic : ReferenceActivePhysicalStep.UpDiagnostic p rate) :
    AffineBatchDecoder.RoundInput (width p) :=
  CoordinatorUpReception.roundInput diagnostic.input
/-- Physical coordinates of records retaining an UP diagnostic. -/
def physicalUpCalendarTimes
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))) :
    List ℕ :=
  records.filterMap (fun record =>
    record.output.coordinator.up.map (fun _ => record.input.time.val))
/-- Times projected from the retained diagnostics themselves. -/
def retainedUpCallTimes
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))) :
    List ℕ :=
  (retainedUpDiagnostics records).map (fun diagnostic => (retainedUpTime diagnostic).val)
/-- Constant extension of a diagnostic's four-field round input. -/
def constantInputTrace
    (input : CoordinatorUpReception.ReceptionInput p rate.eta.val rate.eta.property
      (ReferenceUpReception.sourceCap_forLedger rate) rate.n rate.n_scale) :
    AffineBatchDecoder.Trace p :=
  fun _ => CoordinatorUpReception.roundInput input
/-- Replay one saved call from the accumulator's channel state. -/
def replayOne (bank : CoordinatorUpReception.UpDecoderBank p)
    (diagnostic : ReferenceActivePhysicalStep.UpDiagnostic p rate) :
    CoordinatorUpReception.UpDecoderBank p :=
  Function.update bank (retainedUpFollower diagnostic)
    (AffineBatchDecoder.decodeStep p (constantInputTrace diagnostic.input)
      (bank (retainedUpFollower diagnostic)) (retainedUpTime diagnostic)).1
/-- Replay either the retained call or the no-call frame. -/
def replayOption (bank : CoordinatorUpReception.UpDecoderBank p)
    (diagnostic : Option (ReferenceActivePhysicalStep.UpDiagnostic p rate)) :
    CoordinatorUpReception.UpDecoderBank p :=
  diagnostic.elim bank (replayOne bank)
/-- Fold the actual retained UP diagnostics in their physical calendar order. -/
def replay (initial : CoordinatorUpReception.UpDecoderBank p)
    (diagnostics : List (ReferenceActivePhysicalStep.UpDiagnostic p rate)) :
    CoordinatorUpReception.UpDecoderBank p :=
  diagnostics.foldl replayOne initial
/-- A record without a retained call frames every channel. -/
def replayRecord (bank : CoordinatorUpReception.UpDecoderBank p)
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) :
    CoordinatorUpReception.UpDecoderBank p :=
  match record.output.coordinator.up with
  | none => bank
  | some diagnostic => replayOne bank diagnostic
/-- Positive entries from the retained call to channel `i`, if eligible. -/
def recordUpPositiveEntries
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1)) : List (AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p)) :=
  match record.output.coordinator.up with
  | none => []
  | some diagnostic =>
      if retainedUpFollower diagnostic = i then
        AffineBatchDecoder.positiveAt p (constantInputTrace diagnostic.input)
          (retainedUpTime diagnostic)
      else []
/-- Positive entries from saved channel-`i` calls in calendar order. -/
def retainedUpPositiveEntries
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (i : Fin (p.m - 1)) :
    List (AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p)) :=
  records.flatMap (fun record => recordUpPositiveEntries record i)
/-- Timestamp of one retained call's positive contribution to channel `i`. -/
noncomputable def recordUpPositiveTime
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1)) : Option ℕ := by
  classical
  exact match record.output.coordinator.up with
    | none => none
    | some diagnostic =>
        if retainedUpFollower diagnostic = i then
          if AffineBatchDecoder.eligible (retainedUpRoundInput diagnostic) then
            some record.input.time.val
          else none
        else none
/-- Positive-call timestamps on the actual record calendar. -/
def retainedUpPositiveTimes
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (i : Fin (p.m - 1)) : List ℕ :=
  records.filterMap (fun record => recordUpPositiveTime record i)
/-- Filtering actual UP diagnostics gives the same fold as framing no-call records. -/
theorem replay_records_eq_fold
    (initial : CoordinatorUpReception.UpDecoderBank p)
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))) :
    replay initial (retainedUpDiagnostics records) = records.foldl replayRecord initial := by
  induction records generalizing initial with
  | nil => rfl
  | cons record records ih =>
      cases h : record.output.coordinator.up with
      | none => simpa [retainedUpDiagnostics, replay, replayRecord, h] using ih initial
      | some diagnostic =>
          simpa [retainedUpDiagnostics, replay, replayRecord, h] using
            ih (replayOne initial diagnostic)
/-- Decoder output depends only on the current input coordinate. -/
theorem decodeStep_constantInput_of_current_eq
    (trace : AffineBatchDecoder.Trace p)
    (state : AffineBatchDecoder.State p.T (AffineBatchDecoder.width p))
    (time : Fin p.T)
    (input : CoordinatorUpReception.ReceptionInput p rate.eta.val rate.eta.property
      (ReferenceUpReception.sourceCap_forLedger rate) rate.n rate.n_scale)
    (hcurrent : trace time = CoordinatorUpReception.roundInput input) :
    AffineBatchDecoder.decodeStep p trace state time =
      AffineBatchDecoder.decodeStep p (constantInputTrace input) state time := by
  exact ActiveFollowerDownAcceptance.decodeStep_depends_on_current_input p trace
    (constantInputTrace input) state time hcurrent
/-- Eligibility is the actual gate plus a positive own observation. -/
theorem retainedUpRoundInput_eligible_iff
    (diagnostic : ReferenceActivePhysicalStep.UpDiagnostic p rate) :
    AffineBatchDecoder.eligible (retainedUpRoundInput diagnostic) ↔
      CoordinatorUpReception.receptionGate diagnostic.input ∧
        0 < CoordinatorUpReception.roundedObservationValue p
          diagnostic.input.ownObservation := by
  constructor
  · rintro ⟨hselected, _, hpositive⟩
    exact ⟨(CoordinatorUpReception.roundInput_selected_iff_gate
      diagnostic.input).1 hselected, hpositive⟩
  · rintro ⟨hgate, hpositive⟩
    exact ⟨(CoordinatorUpReception.roundInput_selected_iff_gate
      diagnostic.input).2 hgate, rfl, hpositive⟩
/-- Actual non-invalid reception saves its row-local input and decoder transition. -/
theorem receiveUp_actual_diagnostic_and_replay
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (hpending : ∀ i, i ∉ ledger.pending → (x.state.upDecoderBank i).pending = [])
    (out : ReferenceActivePhysicalStep.Ledger rate × CoordinatorUpReception.UpDecoderBank p)
    (hresult : (ReferenceActivePhysicalStep.receiveUp prepared ledger).result = .success out ∨
      (ReferenceActivePhysicalStep.receiveUp prepared ledger).result = .rejected out) :
    ((ReferenceActivePhysicalStep.receiveUp prepared ledger).diagnostic.map
        ReferenceActivePhysicalStep.UpDiagnostic.input =
          some (ReferenceUpReception.receptionInputAtRow rate x.row
            (ReferenceActivePhysicalStep.upInputs prepared ledger) x.time)) ∧
      ((ReferenceActivePhysicalStep.receiveUp prepared ledger).diagnostic.map
        ReferenceActivePhysicalStep.UpDiagnostic.decoderAfter =
          some (CoordinatorUpReception.decoderTransition
            (ReferenceUpReception.receptionInputAtRow rate x.row
              (ReferenceActivePhysicalStep.upInputs prepared ledger) x.time)).1) ∧
      replayOption x.state.upDecoderBank
        (ReferenceActivePhysicalStep.receiveUp prepared ledger).diagnostic = out.2 := by
  let inputs := ReferenceActivePhysicalStep.upInputs prepared ledger
  let input := ReferenceUpReception.receptionInputAtRow rate x.row inputs x.time
  have hinputCheck : CoordinatorUpReception.receptionInputCheck input = true := by
    cases hcheck : CoordinatorUpReception.receptionInputCheck input with
    | true => rfl
    | false =>
        have hinvalid : (ReferenceActivePhysicalStep.receiveUp prepared ledger).result = .invalid := by
          simp [ReferenceActivePhysicalStep.receiveUp, ReferenceUpReception.receiveUpFilteredAtRow,
            input, inputs, hcheck]
        rcases hresult with hs | hr
        · rw [hinvalid] at hs
          cases hs
        · rw [hinvalid] at hr
          cases hr
  have hbankAfter := ReferenceUpDecoderBankInvariant.actualFilteredReceive_decoderBankAfter
    prepared ledger hpending out hresult
  have hdiagnosticInput :
      (ReferenceActivePhysicalStep.receiveUp prepared ledger).diagnostic.map
        ReferenceActivePhysicalStep.UpDiagnostic.input = some input := by
    simp [ReferenceActivePhysicalStep.receiveUp, input, inputs, hinputCheck]
  have hdiagnosticAfter :
      (ReferenceActivePhysicalStep.receiveUp prepared ledger).diagnostic.map
        ReferenceActivePhysicalStep.UpDiagnostic.decoderAfter =
          some (CoordinatorUpReception.decoderTransition input).1 := by
    simp [ReferenceActivePhysicalStep.receiveUp, input, inputs, hinputCheck]
  have hinputBank : input.upDecoderBank = x.state.upDecoderBank := by
    rfl
  refine ⟨?_, ?_, ?_⟩
  · simpa [input, inputs] using hdiagnosticInput
  · simpa [input, inputs] using hdiagnosticAfter
  have hdiag := (Option.map_eq_some_iff.mp hdiagnosticInput)
  rcases hdiag with ⟨diagnostic, hsome, hsameInput⟩
  change out.2 = CoordinatorUpReception.decoderBankAfter input at hbankAfter
  rw [show (ReferenceActivePhysicalStep.receiveUp prepared ledger).diagnostic =
      some diagnostic from hsome]
  rw [hbankAfter]
  simp only [replayOption, Option.elim_some]
  simp only [replayOne, retainedUpFollower, retainedUpTime]
  rw [hsameInput, ← hinputBank]
  change Function.update input.upDecoderBank input.selectedFollower
      (AffineBatchDecoder.decodeStep p (constantInputTrace input)
        (input.upDecoderBank input.selectedFollower) input.time).1 =
    Function.update input.upDecoderBank input.selectedFollower
      (AffineBatchDecoder.decodeStep p (CoordinatorUpReception.traceAt input)
        (input.upDecoderBank input.selectedFollower) input.time).1
  have hdecode := decodeStep_constantInput_of_current_eq
    (CoordinatorUpReception.traceAt input)
    (input.upDecoderBank input.selectedFollower) input.time input rfl
  rw [← hdecode]
/-- Stage one of the actual collection body changes no pending membership. -/
private theorem startRound_pending_frame
    (ledger ledgerStarted : ReferenceActivePhysicalStep.Ledger rate)
    (time : Fin p.T) (enabled : Bool) (raw : Option (Fin p.K × ℕ))
    (hstart : CoordinatorCollectionLedger.startRound ledger (time.val + 1) enabled raw =
      .success ledgerStarted) :
    ledgerStarted.pending = ledger.pending := by
  unfold CoordinatorCollectionLedger.startRound at hstart
  repeat' (first | split at hstart | simp_all)
  simpa [CoordinatorCollectionLedger.startRoundCandidate] using
    (congrArg (fun l : ReferenceActivePhysicalStep.Ledger rate => l.pending) hstart.symm)
/-- Receiver tags and finish outcomes preserve the returned bank and diagnostic. -/
private theorem collectionFinish_noninvalid_fields
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (recording : CoordinatorRecordingOperation.Output p)
    (cut : ReferenceActivePhysicalStep.UpCut p rate)
    (out : ReferenceActivePhysicalStep.Ledger rate × CoordinatorUpReception.UpDecoderBank p)
    (hresult : cut.result = .success out ∨ cut.result = .rejected out) :
    (ReferenceActivePhysicalStep.collectionFinish (x := x) payload started recording cut).upDecoderBank = out.2 ∧
    (ReferenceActivePhysicalStep.collectionFinish (x := x) payload started recording cut).up =
      cut.diagnostic := by
  rcases hresult with hsuccess | hrejected
  · cases hfinish : CoordinatorCollectionLedger.finishRound out.1 with
    | invalid => simp [ReferenceActivePhysicalStep.collectionFinish, hsuccess, hfinish,
        ReferenceActivePhysicalStep.coordinatorFailure]
    | rejected ledgerRejected =>
        simp [ReferenceActivePhysicalStep.collectionFinish, hsuccess, hfinish,
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
    | rejected ledgerRejected =>
        simp [ReferenceActivePhysicalStep.collectionFinish, hrejected, hfinish,
          ReferenceActivePhysicalStep.coordinatorFailure]
    | success ledgerFinished =>
        cases hclock : CoordinatorPhaseClock.finishRound p rate.eta.val x.time
            started.clock ledgerFinished.pending x.row with
        | error reason =>
            simp [ReferenceActivePhysicalStep.collectionFinish, hrejected, hfinish, hclock,
              ReferenceActivePhysicalStep.coordinatorFailure]
        | ok clockFinished =>
            simp [ReferenceActivePhysicalStep.collectionFinish, hrejected, hfinish, hclock]
/-- Collection dispatch preserves replayed banks through later failures. -/
private theorem collectionPostChoice_replay
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ)
    (hpending : ∀ i, i ∉ ledger.pending → (x.state.upDecoderBank i).pending = [])
    (hordinary : (ReferenceActivePhysicalStep.collectionPostChoice prepared payload ledger
      started weights).configuration ≠ .dagger) :
    (ReferenceActivePhysicalStep.collectionPostChoice prepared payload ledger started weights).upDecoderBank =
      replayOption x.state.upDecoderBank
        (ReferenceActivePhysicalStep.collectionPostChoice prepared payload ledger started weights).up ∧
      (∀ diagnostic, (ReferenceActivePhysicalStep.collectionPostChoice prepared payload ledger
        started weights).up = some diagnostic → diagnostic.input.time = x.time) := by
  classical
  cases hrecord : CoordinatorRecorderComplementBridge.run
      (ReferenceActivePhysicalStep.collectionRecordingInput prepared payload started weights) with
  | none =>
      simp [ReferenceActivePhysicalStep.collectionPostChoice, hrecord,
        ReferenceActivePhysicalStep.coordinatorFailure] at hordinary
  | some recording =>
      let enabled := ReferenceActivePhysicalStep.collectionEnabled ledger x.time
      let raw := CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording
      cases hstart : CoordinatorCollectionLedger.startRound ledger (x.time.val + 1) enabled raw with
      | invalid =>
          simp [ReferenceActivePhysicalStep.collectionPostChoice, hrecord, hstart,
            enabled, raw, ReferenceActivePhysicalStep.coordinatorFailure] at hordinary
      | rejected rejectedLedger =>
          simp [ReferenceActivePhysicalStep.collectionPostChoice, hrecord, hstart,
            enabled, raw, ReferenceActivePhysicalStep.coordinatorFailure] at hordinary
      | success ledgerStarted =>
          have hservice : CoordinatorCollectionLedger.startRound ledger (x.time.val + 1)
              (ReferenceActivePhysicalStep.collectionEnabled ledger x.time)
              (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) =
                .success ledgerStarted := by
            simpa [enabled, raw] using hstart
          rw [ReferenceActivePhysicalStep.collectionPostChoice_after_start
            prepared payload ledger started weights recording ledgerStarted hrecord hservice]
            at hordinary ⊢
          have hstartedPending : ledgerStarted.pending = ledger.pending :=
            startRound_pending_frame ledger ledgerStarted x.time enabled raw hstart
          have hpendingStarted : ∀ i, i ∉ ledgerStarted.pending →
              (x.state.upDecoderBank i).pending = [] := by
            intro i hi
            apply hpending i
            simpa [hstartedPending] using hi
          cases hcut : (ReferenceActivePhysicalStep.receiveUp prepared ledgerStarted).result with
          | invalid =>
              simp [ReferenceActivePhysicalStep.collectionFinish, hcut,
                ReferenceActivePhysicalStep.coordinatorFailure] at hordinary
          | success out =>
              have hreceive := receiveUp_actual_diagnostic_and_replay prepared ledgerStarted
                hpendingStarted out (Or.inl hcut)
              have hfields := collectionFinish_noninvalid_fields payload started recording
                (x := x) (ReferenceActivePhysicalStep.receiveUp prepared ledgerStarted)
                out (Or.inl hcut)
              rw [hfields.1, hfields.2]
              constructor
              · exact hreceive.2.2.symm
              · intro diagnostic hdiagnostic
                have hsameInput : diagnostic.input =
                    ReferenceUpReception.receptionInputAtRow rate x.row
                      (ReferenceActivePhysicalStep.upInputs prepared ledgerStarted) x.time := by
                  have h := hreceive.1
                  rw [hdiagnostic] at h
                  simpa using h
                change diagnostic.input.time = x.time
                rw [hsameInput]
                rfl
          | rejected out =>
              have hreceive := receiveUp_actual_diagnostic_and_replay prepared ledgerStarted
                hpendingStarted out (Or.inr hcut)
              have hfields := collectionFinish_noninvalid_fields payload started recording
                (x := x) (ReferenceActivePhysicalStep.receiveUp prepared ledgerStarted)
                out (Or.inr hcut)
              rw [hfields.1, hfields.2]
              constructor
              · exact hreceive.2.2.symm
              · intro diagnostic hdiagnostic
                have hsameInput : diagnostic.input =
                    ReferenceUpReception.receptionInputAtRow rate x.row
                      (ReferenceActivePhysicalStep.upInputs prepared ledgerStarted) x.time := by
                  have h := hreceive.1
                  rw [hdiagnostic] at h
                  simpa using h
                change diagnostic.input.time = x.time
                rw [hsameInput]
                rfl
/-- Actual live-tail outcomes make no coordinator UP call. -/
private theorem livePostChoice_replay
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
    (base : Fin (p.m - 1) → ℕ)
    (started : CoordinatorPhaseClock.StartRoundResult p) :
    (ReferenceActivePhysicalStep.livePostChoice prepared registers owned base started).upDecoderBank =
      replayOption x.state.upDecoderBank
        (ReferenceActivePhysicalStep.livePostChoice prepared registers owned base started).up ∧
      (ReferenceActivePhysicalStep.livePostChoice prepared registers owned base started).up = none := by
  classical
  unfold ReferenceActivePhysicalStep.livePostChoice
  repeat' (first | split | simp [ReferenceActivePhysicalStep.coordinatorFailure,
    replayOption])
/-- Ordinary dispatcher outputs retain actual calls and their advanced banks. -/
private theorem observeCoordinator_replay
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (hinvariant : ReferenceUpDecoderBankInvariant.upBankInvariant x.state)
    (hordinary : prepared.observeCoordinator.configuration ≠ .dagger) :
    prepared.observeCoordinator.upDecoderBank =
      replayOption x.state.upDecoderBank prepared.observeCoordinator.up ∧
      (∀ diagnostic, prepared.observeCoordinator.up = some diagnostic →
        diagnostic.input.time = x.time) := by
  classical
  cases hphase : x.state.coordinator with
  | first =>
      cases hdispatch : CoordinatorRoundDispatch.dispatch
          (.first (ReferenceActivePhysicalStep.firstInput x)) with
      | first outcome =>
          cases outcome with
          | chosen installed selected =>
              have hcut : prepared.coordinator = .first (.chosen installed selected) := by
                have h := prepared.coordinator_eq
                simp only [ReferenceActivePhysicalStep.dispatch, hphase] at h
                rw [hdispatch] at h
                exact h
              rw [ReferenceActivePhysicalStep.observeCoordinator_first_equation
                prepared (.chosen installed selected) hcut]
              by_cases hselection : (ReferenceActivePhysicalStep.DispatchCut.first
                  (.chosen installed selected)).selection = none
              · simp [hselection, ReferenceActivePhysicalStep.coordinatorFailure, replayOption]
              · have hpost := livePostChoice_replay prepared installed.registers
                  installed.ownedRegisters installed.followerBaseScore installed.startRoundResult
                constructor
                · simpa [hselection] using hpost.1
                · intro diagnostic hdiagnostic
                  have hdiagPost :
                      (ReferenceActivePhysicalStep.livePostChoice prepared installed.registers
                        installed.ownedRegisters installed.followerBaseScore
                        installed.startRoundResult).up = some diagnostic := by
                    simpa [hselection] using hdiagnostic
                  rw [hpost.2] at hdiagPost
                  cases hdiagPost
          | choiceDomainFailure installed =>
              have hcut : prepared.coordinator = .first (.choiceDomainFailure installed) := by
                have h := prepared.coordinator_eq
                simp only [ReferenceActivePhysicalStep.dispatch, hphase] at h
                rw [hdispatch] at h
                exact h
              rw [ReferenceActivePhysicalStep.observeCoordinator_first_equation
                prepared (.choiceDomainFailure installed) hcut]
              simp [ReferenceActivePhysicalStep.DispatchCut.selection,
                ReferenceActivePhysicalStep.coordinatorFailure, replayOption]
          | recorderBoundaryFailure installed =>
              have hcut : prepared.coordinator = .first (.recorderBoundaryFailure installed) := by
                have h := prepared.coordinator_eq
                simp only [ReferenceActivePhysicalStep.dispatch, hphase] at h
                rw [hdispatch] at h
                exact h
              rw [ReferenceActivePhysicalStep.observeCoordinator_first_equation
                prepared (.recorderBoundaryFailure installed) hcut]
              simp [ReferenceActivePhysicalStep.DispatchCut.selection,
                ReferenceActivePhysicalStep.coordinatorFailure, replayOption]
          | choiceRejected installed =>
              have hcut : prepared.coordinator = .first (.choiceRejected installed) := by
                have h := prepared.coordinator_eq
                simp only [ReferenceActivePhysicalStep.dispatch, hphase] at h
                rw [hdispatch] at h
                exact h
              rw [ReferenceActivePhysicalStep.observeCoordinator_first_equation
                prepared (.choiceRejected installed) hcut]
              simp [ReferenceActivePhysicalStep.DispatchCut.selection,
                ReferenceActivePhysicalStep.coordinatorFailure, replayOption]
  | live registers owned base =>
      cases hdispatch : CoordinatorRoundDispatch.dispatch
          (.live (ReferenceActivePhysicalStep.liveInput x registers owned base)) with
      | live outcome =>
          cases outcome with
          | continuingChosen dispatched hstart continuation selected =>
              have hcut : prepared.coordinator = .live registers owned base
                  (.continuingChosen dispatched hstart continuation selected) := by
                have h := prepared.coordinator_eq
                simp only [ReferenceActivePhysicalStep.dispatch, hphase] at h
                rw [hdispatch] at h
                exact h
              rw [ReferenceActivePhysicalStep.observeCoordinator_live_equation
                prepared registers owned base
                (.continuingChosen dispatched hstart continuation selected) hcut]
              by_cases hselection : (ReferenceActivePhysicalStep.DispatchCut.live registers
                  owned base (.continuingChosen dispatched hstart continuation selected)).selection = none
              · simp [hselection, ReferenceActivePhysicalStep.coordinatorFailure, replayOption]
              · have hpost := livePostChoice_replay prepared
                  (ReferenceActivePhysicalStep.liveRegistersAt registers x.time)
                  (ReferenceActivePhysicalStep.liveOwnedAt registers owned x.time)
                  base dispatched.startResult
                constructor
                · simpa [hselection] using hpost.1
                · intro diagnostic hdiagnostic
                  have hdiagPost :
                      (ReferenceActivePhysicalStep.livePostChoice prepared
                        (ReferenceActivePhysicalStep.liveRegistersAt registers x.time)
                        (ReferenceActivePhysicalStep.liveOwnedAt registers owned x.time)
                        base dispatched.startResult).up = some diagnostic := by
                    simpa [hselection] using hdiagnostic
                  rw [hpost.2] at hdiagPost
                  cases hdiagPost
          | cutoffChosen dispatched hstart ledger hinitialization ledgerEq hdomain
              hclock hpending noAssignment selected =>
              have hcut : prepared.coordinator = .live registers owned base
                  (.cutoffChosen dispatched hstart ledger hinitialization ledgerEq hdomain
                    hclock hpending noAssignment selected) := by
                have h := prepared.coordinator_eq
                simp only [ReferenceActivePhysicalStep.dispatch, hphase] at h
                rw [hdispatch] at h
                exact h
              rw [ReferenceActivePhysicalStep.observeCoordinator_live_equation
                prepared registers owned base
                (.cutoffChosen dispatched hstart ledger hinitialization ledgerEq hdomain
                  hclock hpending noAssignment selected) hcut]
              by_cases hselection : (ReferenceActivePhysicalStep.DispatchCut.live registers
                  owned base (.cutoffChosen dispatched hstart ledger hinitialization ledgerEq hdomain
                    hclock hpending noAssignment selected)).selection = none
              · simp [hselection, ReferenceActivePhysicalStep.coordinatorFailure, replayOption]
              · have hsharedPending :
                    (ReferenceActivePhysicalStep.sharedLedger ledger).pending = Finset.univ := by
                  simp [ReferenceActivePhysicalStep.sharedLedger, ledgerEq,
                    CoordinatorStartRoundCutoffDispatch.collectionStartLedger]
                have hpendingShared : ∀ i,
                    i ∉ (ReferenceActivePhysicalStep.sharedLedger ledger).pending →
                      (x.state.upDecoderBank i).pending = [] := by
                  intro i hi
                  simp [hsharedPending] at hi
                have hOrdinaryPost :
                    (ReferenceActivePhysicalStep.collectionPostChoice prepared registers.payload
                      (ReferenceActivePhysicalStep.sharedLedger ledger) dispatched.startResult
                      (ReferenceActivePhysicalStep.liveRegistersAt registers x.time).complementWeights).configuration
                      ≠ .dagger := by
                  have h := hordinary
                  rw [ReferenceActivePhysicalStep.observeCoordinator_live_equation
                    prepared registers owned base
                    (.cutoffChosen dispatched hstart ledger hinitialization ledgerEq hdomain
                      hclock hpending noAssignment selected) hcut] at h
                  simpa [hselection] using h
                have hpost := collectionPostChoice_replay prepared registers.payload
                  (ReferenceActivePhysicalStep.sharedLedger ledger) dispatched.startResult
                  (ReferenceActivePhysicalStep.liveRegistersAt registers x.time).complementWeights
                  hpendingShared hOrdinaryPost
                simpa [hselection] using hpost
          | clockFailure failure hfail =>
              have hcut : prepared.coordinator = .live registers owned base
                  (.clockFailure failure hfail) := by
                have h := prepared.coordinator_eq
                simp only [ReferenceActivePhysicalStep.dispatch, hphase] at h
                rw [hdispatch] at h
                exact h
              rw [ReferenceActivePhysicalStep.observeCoordinator_live_equation
                prepared registers owned base (.clockFailure failure hfail) hcut]
              simp [ReferenceActivePhysicalStep.DispatchCut.selection,
                ReferenceActivePhysicalStep.coordinatorFailure, replayOption]
          | initializerFailure dispatched hstart checked hchecked =>
              have hcut : prepared.coordinator = .live registers owned base
                  (.initializerFailure dispatched hstart checked hchecked) := by
                have h := prepared.coordinator_eq
                simp only [ReferenceActivePhysicalStep.dispatch, hphase] at h
                rw [hdispatch] at h
                exact h
              rw [ReferenceActivePhysicalStep.observeCoordinator_live_equation
                prepared registers owned base
                (.initializerFailure dispatched hstart checked hchecked) hcut]
              simp [ReferenceActivePhysicalStep.DispatchCut.selection,
                ReferenceActivePhysicalStep.coordinatorFailure, replayOption]
          | localFailure dispatched hstart reason =>
              have hcut : prepared.coordinator = .live registers owned base
                  (.localFailure dispatched hstart reason) := by
                have h := prepared.coordinator_eq
                simp only [ReferenceActivePhysicalStep.dispatch, hphase] at h
                rw [hdispatch] at h
                exact h
              rw [ReferenceActivePhysicalStep.observeCoordinator_live_equation
                prepared registers owned base (.localFailure dispatched hstart reason) hcut]
              simp [ReferenceActivePhysicalStep.DispatchCut.selection,
                ReferenceActivePhysicalStep.coordinatorFailure, replayOption]
  | collection payload ledger proposal =>
      have hpending : ∀ i, i ∉ ledger.pending → (x.state.upDecoderBank i).pending = [] := by
        have h := hinvariant
        simp [ReferenceUpDecoderBankInvariant.upBankInvariant,
          ReferenceUpDecoderBankInvariant.coordinatorBankInvariant, hphase] at h
        exact h.2
      by_cases hcutoff : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
      · let cutoff : Fin p.T := ⟨ledger.cutoff - 1, by omega⟩
        let clock := ReferenceActivePhysicalStep.collectionClock payload ledger proposal cutoff
        cases hdispatch : CoordinatorRoundDispatch.dispatch
            (.collection (ReferenceActivePhysicalStep.collectionInput x payload ledger clock cutoff)) with
        | collection outcome =>
            cases outcome with
            | continuing core snapshot boundary scores =>
                have hcut : prepared.coordinator = .collection payload ledger clock cutoff
                    (.continuing core snapshot boundary scores) := by
                  have h := prepared.coordinator_eq
                  simp [ReferenceActivePhysicalStep.dispatch, hphase, hcutoff] at h
                  rw [hdispatch] at h
                  exact h
                rw [ReferenceActivePhysicalStep.observeCoordinator_collection_equation
                  prepared payload ledger clock cutoff (.continuing core snapshot boundary scores) hcut]
                by_cases hselection : (ReferenceActivePhysicalStep.DispatchCut.collection
                    payload ledger clock cutoff
                    (.continuing core snapshot boundary scores)).selection = none
                · simp [hselection, ReferenceActivePhysicalStep.coordinatorFailure, replayOption]
                · have hOrdinaryPost :
                      (ReferenceActivePhysicalStep.collectionPostChoice prepared payload ledger
                        snapshot.clockStarted
                        (CoordinatorCollectionInteractive.PreObservationInputs.weights
                          (ReferenceActivePhysicalStep.collectionInput x payload ledger clock cutoff)
                          snapshot.inputsValid.ledger_valid snapshot.inputsValid.assignment_eq)).configuration
                        ≠ .dagger := by
                    have h := hordinary
                    rw [ReferenceActivePhysicalStep.observeCoordinator_collection_equation
                      prepared payload ledger clock cutoff
                      (.continuing core snapshot boundary scores) hcut] at h
                    simpa [hselection] using h
                  have hpost := collectionPostChoice_replay prepared payload ledger
                    snapshot.clockStarted
                    (CoordinatorCollectionInteractive.PreObservationInputs.weights
                      (ReferenceActivePhysicalStep.collectionInput x payload ledger clock cutoff)
                      snapshot.inputsValid.ledger_valid snapshot.inputsValid.assignment_eq)
                    hpending hOrdinaryPost
                  simpa [hselection] using hpost
            | laterChosen core consistent started hstart instruction hinstruction output
                localEq clockData installed selected =>
                have hcut : prepared.coordinator = .collection payload ledger clock cutoff
                    (.laterChosen core consistent started hstart instruction hinstruction output
                      localEq clockData installed selected) := by
                  have h := prepared.coordinator_eq
                  simp [ReferenceActivePhysicalStep.dispatch, hphase, hcutoff] at h
                  rw [hdispatch] at h
                  exact h
                rw [ReferenceActivePhysicalStep.observeCoordinator_collection_equation
                  prepared payload ledger clock cutoff
                  (.laterChosen core consistent started hstart instruction hinstruction output
                    localEq clockData installed selected) hcut]
                by_cases hselection : (ReferenceActivePhysicalStep.DispatchCut.collection
                    payload ledger clock cutoff
                    (.laterChosen core consistent started hstart instruction hinstruction output
                      localEq clockData installed selected)).selection = none
                · simp [hselection, ReferenceActivePhysicalStep.coordinatorFailure, replayOption]
                · have hpost := livePostChoice_replay prepared installed.registers
                    installed.ownedRegisters installed.retainedBaseScore started
                  constructor
                  · simpa [hselection] using hpost.1
                  · intro diagnostic hdiagnostic
                    have hdiagPost :
                        (ReferenceActivePhysicalStep.livePostChoice prepared
                          installed.registers installed.ownedRegisters
                          installed.retainedBaseScore started).up = some diagnostic := by
                      simpa [hselection] using hdiagnostic
                    rw [hpost.2] at hdiagPost
                    cases hdiagPost
            | clockFailure failure hstart =>
                have hcut : prepared.coordinator = .collection payload ledger clock cutoff
                    (.clockFailure failure hstart) := by
                  have h := prepared.coordinator_eq
                  simp [ReferenceActivePhysicalStep.dispatch, hphase, hcutoff] at h
                  rw [hdispatch] at h
                  exact h
                rw [ReferenceActivePhysicalStep.observeCoordinator_collection_equation
                  prepared payload ledger clock cutoff (.clockFailure failure hstart) hcut]
                simp [ReferenceActivePhysicalStep.DispatchCut.selection,
                  ReferenceActivePhysicalStep.coordinatorFailure, replayOption]
            | localFailure started hstart hinvalid reason =>
                have hcut : prepared.coordinator = .collection payload ledger clock cutoff
                    (.localFailure started hstart hinvalid reason) := by
                  have h := prepared.coordinator_eq
                  simp [ReferenceActivePhysicalStep.dispatch, hphase, hcutoff] at h
                  rw [hdispatch] at h
                  exact h
                rw [ReferenceActivePhysicalStep.observeCoordinator_collection_equation
                  prepared payload ledger clock cutoff (.localFailure started hstart hinvalid reason) hcut]
                simp [ReferenceActivePhysicalStep.DispatchCut.selection,
                  ReferenceActivePhysicalStep.coordinatorFailure, replayOption]
            | coreFailure core started hstart reason =>
                have hcut : prepared.coordinator = .collection payload ledger clock cutoff
                    (.coreFailure core started hstart reason) := by
                  have h := prepared.coordinator_eq
                  simp [ReferenceActivePhysicalStep.dispatch, hphase, hcutoff] at h
                  rw [hdispatch] at h
                  exact h
                rw [ReferenceActivePhysicalStep.observeCoordinator_collection_equation
                  prepared payload ledger clock cutoff (.coreFailure core started hstart reason) hcut]
                simp [ReferenceActivePhysicalStep.DispatchCut.selection,
                  ReferenceActivePhysicalStep.coordinatorFailure, replayOption]
            | laterReconstructionFailure core consistent started hstart instruction hinstruction reason hlater =>
                have hcut : prepared.coordinator = .collection payload ledger clock cutoff
                    (.laterReconstructionFailure core consistent started hstart instruction hinstruction reason hlater) := by
                  have h := prepared.coordinator_eq
                  simp [ReferenceActivePhysicalStep.dispatch, hphase, hcutoff] at h
                  rw [hdispatch] at h
                  exact h
                rw [ReferenceActivePhysicalStep.observeCoordinator_collection_equation
                  prepared payload ledger clock cutoff
                  (.laterReconstructionFailure core consistent started hstart instruction hinstruction reason hlater) hcut]
                simp [ReferenceActivePhysicalStep.DispatchCut.selection,
                  ReferenceActivePhysicalStep.coordinatorFailure, replayOption]
            | laterPrefixFailure core consistent started hstart instruction hinstruction arm reason hlater =>
                have hcut : prepared.coordinator = .collection payload ledger clock cutoff
                    (.laterPrefixFailure core consistent started hstart instruction hinstruction arm reason hlater) := by
                  have h := prepared.coordinator_eq
                  simp [ReferenceActivePhysicalStep.dispatch, hphase, hcutoff] at h
                  rw [hdispatch] at h
                  exact h
                rw [ReferenceActivePhysicalStep.observeCoordinator_collection_equation
                  prepared payload ledger clock cutoff
                  (.laterPrefixFailure core consistent started hstart instruction hinstruction arm reason hlater) hcut]
                simp [ReferenceActivePhysicalStep.DispatchCut.selection,
                  ReferenceActivePhysicalStep.coordinatorFailure, replayOption]
            | laterOrientationFailure core consistent started hstart instruction hinstruction set hlater =>
                have hcut : prepared.coordinator = .collection payload ledger clock cutoff
                    (.laterOrientationFailure core consistent started hstart instruction hinstruction set hlater) := by
                  have h := prepared.coordinator_eq
                  simp [ReferenceActivePhysicalStep.dispatch, hphase, hcutoff] at h
                  rw [hdispatch] at h
                  exact h
                rw [ReferenceActivePhysicalStep.observeCoordinator_collection_equation
                  prepared payload ledger clock cutoff
                  (.laterOrientationFailure core consistent started hstart instruction hinstruction set hlater) hcut]
                simp [ReferenceActivePhysicalStep.DispatchCut.selection,
                  ReferenceActivePhysicalStep.coordinatorFailure, replayOption]
            | laterChoiceFailure core consistent started hstart instruction hinstruction output
                localEq clockData installed reason =>
                have hcut : prepared.coordinator = .collection payload ledger clock cutoff
                    (.laterChoiceFailure core consistent started hstart instruction hinstruction
                      output localEq clockData installed reason) := by
                  have h := prepared.coordinator_eq
                  simp [ReferenceActivePhysicalStep.dispatch, hphase, hcutoff] at h
                  rw [hdispatch] at h
                  exact h
                rw [ReferenceActivePhysicalStep.observeCoordinator_collection_equation
                  prepared payload ledger clock cutoff
                  (.laterChoiceFailure core consistent started hstart instruction hinstruction
                    output localEq clockData installed reason) hcut]
                simp [ReferenceActivePhysicalStep.DispatchCut.selection,
                  ReferenceActivePhysicalStep.coordinatorFailure, replayOption]
      · have hcut : prepared.coordinator = .invalidCollectionCutoff := by
          simpa [ReferenceActivePhysicalStep.dispatch, hphase, hcutoff] using
            prepared.coordinator_eq
        simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator, hcut,
          ReferenceActivePhysicalStep.DispatchCut.selection,
          ReferenceActivePhysicalStep.coordinatorFailure, replayOption]
  | dagger =>
      have hcut : prepared.coordinator = .dagger := by
        simpa [ReferenceActivePhysicalStep.dispatch, hphase] using prepared.coordinator_eq
      rw [ReferenceActivePhysicalStep.observeCoordinator_dagger prepared hcut] at hordinary
      simp at hordinary
/-- Ordinary successor replay also identifies every retained call's time. -/
theorem ordinaryRecord_replay_and_diagnostic_time
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hinvariant : ReferenceUpDecoderBankInvariant.upBankInvariant record.input.state)
    (hordinary : record.output.next.coordinator ≠ .dagger) :
    record.output.next.upDecoderBank =
        replayOption record.input.state.upDecoderBank record.output.coordinator.up ∧
      ∀ diagnostic, record.output.coordinator.up = some diagnostic →
        diagnostic.input.time = record.input.time := by
  have hstepOrdinary : (ReferenceActivePhysicalStep.step record.input).next.coordinator ≠
      .dagger := by
    simpa [record.output_eq] using hordinary
  have hpreparedOrdinary :
      (ReferenceActivePhysicalStep.prepare record.input).observeCoordinator.configuration ≠
        .dagger := by
    rw [← (ReferenceActivePhysicalStep.step_next_fields record.input).1]
    exact hstepOrdinary
  have hprepared := observeCoordinator_replay
    (ReferenceActivePhysicalStep.prepare record.input) hinvariant hpreparedOrdinary
  have hbank : record.output.next.upDecoderBank =
      (ReferenceActivePhysicalStep.step record.input).next.upDecoderBank := by
    rw [record.output_eq]
  have hcall : record.output.coordinator.up =
      (ReferenceActivePhysicalStep.step record.input).coordinator.up := by
    rw [record.output_eq]
  have hdecoderBank : record.output.next.upDecoderBank =
      replayOption record.input.state.upDecoderBank record.output.coordinator.up := by
    calc
      record.output.next.upDecoderBank =
          (ReferenceActivePhysicalStep.step record.input).next.upDecoderBank := hbank
      _ = replayOption record.input.state.upDecoderBank
          (ReferenceActivePhysicalStep.step record.input).coordinator.up := hprepared.1
      _ = replayOption record.input.state.upDecoderBank record.output.coordinator.up := by
        rw [← hcall]
  refine ⟨hdecoderBank, ?_⟩
  intro diagnostic hdiagnostic
  have hdiagnostic' : (ReferenceActivePhysicalStep.step record.input).coordinator.up =
      some diagnostic := by
    rw [← hcall]
    exact hdiagnostic
  exact hprepared.2 diagnostic hdiagnostic'
/-- The ordinary physical successor is the replay of its retained call. -/
theorem ordinaryRecord_upDecoderBank_replay
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hinvariant : ReferenceUpDecoderBankInvariant.upBankInvariant record.input.state)
    (hordinary : record.output.next.coordinator ≠ .dagger) :
    record.output.next.upDecoderBank =
      replayOption record.input.state.upDecoderBank record.output.coordinator.up := by
  exact (ordinaryRecord_replay_and_diagnostic_time record hinvariant hordinary).1
/-- A retained diagnostic's time is the literal serviced physical coordinate. -/
theorem ordinaryRecord_upDiagnostic_time
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hinvariant : ReferenceUpDecoderBankInvariant.upBankInvariant record.input.state)
    (hordinary : record.output.next.coordinator ≠ .dagger)
    (diagnostic : ReferenceActivePhysicalStep.UpDiagnostic p rate)
    (hdiagnostic : record.output.coordinator.up = some diagnostic) :
    diagnostic.input.time = record.input.time := by
  exact (ordinaryRecord_replay_and_diagnostic_time record hinvariant hordinary).2
    diagnostic hdiagnostic
/-- Collected history appends exactly the positive entry from an ordinary call. -/
theorem ordinaryRecord_collected_upPositiveEntries
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hinvariant : ReferenceUpDecoderBankInvariant.upBankInvariant record.input.state)
    (hordinary : record.output.next.coordinator ≠ .dagger)
    (i : Fin (p.m - 1)) :
    AffineBatchDecoder.collected (record.output.next.upDecoderBank i) =
      AffineBatchDecoder.collected (record.input.state.upDecoderBank i) ++
        recordUpPositiveEntries record i := by
  have hbankWF : CoordinatorUpReception.decoderBankWellFormed p
      record.input.state.upDecoderBank := by
    change ReferenceUpDecoderBankInvariant.coordinatorBankInvariant
      record.input.state.coordinator record.input.state.upDecoderBank at hinvariant
    exact hinvariant.1
  have hchannelWF := hbankWF i
  have hbank := ordinaryRecord_upDecoderBank_replay record hinvariant hordinary
  cases hdiagnostic : record.output.coordinator.up with
  | none =>
      have hchannel : record.output.next.upDecoderBank i =
          record.input.state.upDecoderBank i := by
        have h := congrFun hbank i
        simpa [replayOption, hdiagnostic] using h
      rw [hchannel]
      simp [recordUpPositiveEntries, hdiagnostic]
  | some diagnostic =>
      have hchannelReplay : record.output.next.upDecoderBank i =
          replayOne record.input.state.upDecoderBank diagnostic i := by
        have h := congrFun hbank i
        simpa [replayOption, hdiagnostic] using h
      by_cases hselected : retainedUpFollower diagnostic = i
      · have hchannel : record.output.next.upDecoderBank i =
            (AffineBatchDecoder.decodeStep p (constantInputTrace diagnostic.input)
              (record.input.state.upDecoderBank i) (retainedUpTime diagnostic)).1 := by
          rw [hchannelReplay]
          have hselected' : diagnostic.input.selectedFollower = i := hselected
          simp [replayOne, retainedUpFollower, retainedUpTime, hselected']
        have hstep := AffineBatchDecoder.step_spec p
          (constantInputTrace diagnostic.input) (record.input.state.upDecoderBank i)
          (retainedUpTime diagnostic) hchannelWF.1 hchannelWF.2
        calc
          AffineBatchDecoder.collected (record.output.next.upDecoderBank i) =
              AffineBatchDecoder.collected
                ((AffineBatchDecoder.decodeStep p (constantInputTrace diagnostic.input)
                  (record.input.state.upDecoderBank i) (retainedUpTime diagnostic)).1) := by
                rw [hchannel]
          _ = AffineBatchDecoder.collected (record.input.state.upDecoderBank i) ++
                AffineBatchDecoder.positiveAt p (constantInputTrace diagnostic.input)
                  (retainedUpTime diagnostic) := by
                simpa only [AffineBatchDecoder.decodeStep] using hstep.2.2
          _ = AffineBatchDecoder.collected (record.input.state.upDecoderBank i) ++
                recordUpPositiveEntries record i := by
                simp [recordUpPositiveEntries, hdiagnostic, hselected]
      · have hchannel : record.output.next.upDecoderBank i =
            record.input.state.upDecoderBank i := by
          rw [hchannelReplay]
          have hselected' : diagnostic.input.selectedFollower ≠ i := by
            simpa [retainedUpFollower] using hselected
          change Function.update record.input.state.upDecoderBank
              diagnostic.input.selectedFollower
              (AffineBatchDecoder.decodeStep p (constantInputTrace diagnostic.input)
                (record.input.state.upDecoderBank diagnostic.input.selectedFollower)
                diagnostic.input.time).1 i = record.input.state.upDecoderBank i
          exact Function.update_of_ne hselected'.symm _ _
        rw [hchannel]
        simp [recordUpPositiveEntries, hdiagnostic, hselected]
/-- A channel's positive entries carry the saved call's physical timestamp. -/
theorem ordinaryRecord_upPositiveEntries_time_map
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hinvariant : ReferenceUpDecoderBankInvariant.upBankInvariant record.input.state)
    (hordinary : record.output.next.coordinator ≠ .dagger)
    (i : Fin (p.m - 1)) :
    (recordUpPositiveEntries record i).map (fun entry => entry.time.val) =
      (recordUpPositiveTime record i).toList := by
  classical
  cases hdiagnostic : record.output.coordinator.up with
  | none =>
      simp [recordUpPositiveEntries, recordUpPositiveTime, hdiagnostic]
  | some diagnostic =>
      have htime := ordinaryRecord_upDiagnostic_time record hinvariant hordinary
        diagnostic hdiagnostic
      by_cases hselected : retainedUpFollower diagnostic = i
      · by_cases hpositive : AffineBatchDecoder.eligible
            (retainedUpRoundInput diagnostic)
        · have hpositive' : AffineBatchDecoder.eligible
              (CoordinatorUpReception.roundInput diagnostic.input) := by
            simpa [retainedUpRoundInput] using hpositive
          simp [recordUpPositiveEntries, recordUpPositiveTime, hdiagnostic,
            hselected, hpositive', AffineBatchDecoder.positiveAt,
            AffineBatchDecoder.entry, retainedUpTime, retainedUpRoundInput,
            constantInputTrace, htime]
        · have hpositive' : ¬ AffineBatchDecoder.eligible
              (CoordinatorUpReception.roundInput diagnostic.input) := by
            simpa [retainedUpRoundInput] using hpositive
          simp [recordUpPositiveEntries, recordUpPositiveTime, hdiagnostic,
            hselected, hpositive', AffineBatchDecoder.positiveAt,
            retainedUpRoundInput, constantInputTrace]
      · simp [recordUpPositiveEntries, recordUpPositiveTime, hdiagnostic, hselected]
/-- Any emitted positive-time option is stamped with its record's physical
calendar coordinate. -/
theorem recordUpPositiveTime_eq_recordTime
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1)) (time : ℕ)
    (hpositive : recordUpPositiveTime record i = some time) :
    time = record.input.time.val := by
  classical
  cases hdiagnostic : record.output.coordinator.up with
  | none => simp [recordUpPositiveTime, hdiagnostic] at hpositive
  | some diagnostic =>
      simp only [recordUpPositiveTime, hdiagnostic] at hpositive
      by_cases hselected : retainedUpFollower diagnostic = i
      · rw [ite_eq_left hselected] at hpositive
        by_cases heligible : AffineBatchDecoder.eligible (retainedUpRoundInput diagnostic)
        · rw [ite_eq_left heligible] at hpositive
          exact (Option.some.inj hpositive).symm
        · rw [ite_eq_right heligible] at hpositive
          cases hpositive
      · rw [ite_eq_right hselected] at hpositive
        cases hpositive
/-- Positive-entry timestamps equal the option-filtered record times. -/
theorem retainedUpPositiveEntries_time_map
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (hinvariant : ∀ record, record ∈ records →
      ReferenceUpDecoderBankInvariant.upBankInvariant record.input.state)
    (hordinary : ∀ record, record ∈ records → record.output.next.coordinator ≠ .dagger)
    (i : Fin (p.m - 1)) :
    (retainedUpPositiveEntries records i).map (fun entry => entry.time.val) =
      retainedUpPositiveTimes records i := by
  induction records with
  | nil => rfl
  | cons record records ih =>
      have hrecordInvariant := hinvariant record (by simp)
      have hrecordOrdinary := hordinary record (by simp)
      have htailInvariant : ∀ current, current ∈ records →
          ReferenceUpDecoderBankInvariant.upBankInvariant current.input.state := by
        intro current hcurrent
        exact hinvariant current (by simp [hcurrent])
      have htailOrdinary : ∀ current, current ∈ records →
          current.output.next.coordinator ≠ .dagger := by
        intro current hcurrent
        exact hordinary current (by simp [hcurrent])
      calc
        (retainedUpPositiveEntries (record :: records) i).map
            (fun entry => entry.time.val) =
            (recordUpPositiveEntries record i).map (fun entry => entry.time.val) ++
              (retainedUpPositiveEntries records i).map (fun entry => entry.time.val) := by
                simp [retainedUpPositiveEntries]
        _ = (recordUpPositiveTime record i).toList ++ retainedUpPositiveTimes records i := by
              rw [ordinaryRecord_upPositiveEntries_time_map record hrecordInvariant
                hrecordOrdinary i, ih htailInvariant htailOrdinary]
        _ = retainedUpPositiveTimes (record :: records) i := by
              cases htime : recordUpPositiveTime record i <;>
                simp [retainedUpPositiveTimes, htime]
/-- Eligible positive calls preserve strict record-time order. -/
theorem retainedUpPositiveTimes_pairwise
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (hrecords : records.Pairwise
      (fun earlier later => earlier.input.time.val < later.input.time.val))
    (i : Fin (p.m - 1)) :
    (retainedUpPositiveTimes records i).Pairwise (· < ·) := by
  apply List.Pairwise.filterMap (fun record => recordUpPositiveTime record i)
  · intro earlier later htime earlierTime hearlier laterTime hlater
    have hearlierEq := recordUpPositiveTime_eq_recordTime earlier i earlierTime hearlier
    have hlaterEq := recordUpPositiveTime_eq_recordTime later i laterTime hlater
    rw [hearlierEq, hlaterEq]
    exact htime
  · exact hrecords
/-- Retained diagnostic times are the actual calendar restricted to calls. -/
theorem retainedUpCallTimes_eq_physicalUpCalendarTimes
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (hinvariant : ∀ record, record ∈ records →
      ReferenceUpDecoderBankInvariant.upBankInvariant record.input.state)
    (hordinary : ∀ record, record ∈ records → record.output.next.coordinator ≠ .dagger) :
    retainedUpCallTimes records = physicalUpCalendarTimes records := by
  induction records with
  | nil => rfl
  | cons record records ih =>
      have hrecordInvariant := hinvariant record (by simp)
      have hrecordOrdinary := hordinary record (by simp)
      have htailInvariant : ∀ current, current ∈ records →
          ReferenceUpDecoderBankInvariant.upBankInvariant current.input.state := by
        intro current hcurrent
        exact hinvariant current (by simp [hcurrent])
      have htailOrdinary : ∀ current, current ∈ records →
          current.output.next.coordinator ≠ .dagger := by
        intro current hcurrent
        exact hordinary current (by simp [hcurrent])
      cases hdiagnostic : record.output.coordinator.up with
      | none =>
          simpa [retainedUpCallTimes, physicalUpCalendarTimes,
            retainedUpDiagnostics, hdiagnostic] using ih htailInvariant htailOrdinary
      | some diagnostic =>
          have htime := ordinaryRecord_upDiagnostic_time record hrecordInvariant
            hrecordOrdinary diagnostic hdiagnostic
          have htimeVal : (retainedUpTime diagnostic).val = record.input.time.val :=
            congrArg Fin.val htime
          calc
            retainedUpCallTimes (record :: records) =
                (retainedUpTime diagnostic).val :: retainedUpCallTimes records := by
              simp [retainedUpCallTimes, retainedUpDiagnostics, hdiagnostic]
            _ = record.input.time.val :: physicalUpCalendarTimes records := by
              rw [htimeVal, ih htailInvariant htailOrdinary]
            _ = physicalUpCalendarTimes (record :: records) := by
              simp [physicalUpCalendarTimes, hdiagnostic]
/-- A connected actual prefix that ends outside dagger has no dagger state at
any of its record successors. This is derived from the absorbing physical
transition, not imposed on the trace. -/
private theorem connected_replay_fold
    {initial final : ReferenceActivePhysicalStep.State p rate}
    {records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))}
    (hchain : ReferenceActivePhysicalHorizon.Connected initial records final)
    (hinvariant : ∀ record, record ∈ records →
      ReferenceUpDecoderBankInvariant.upBankInvariant record.input.state)
    (hordinary : final.coordinator ≠ .dagger) :
    final.upDecoderBank = records.foldl replayRecord initial.upDecoderBank := by
  induction records generalizing initial with
  | nil =>
      simp only [ReferenceActivePhysicalHorizon.Connected] at hchain
      subst final
      rfl
  | cons record records ih =>
      simp only [ReferenceActivePhysicalHorizon.Connected] at hchain
      rcases hchain with ⟨hinput, htail⟩
      have hsuccessorOrdinary : record.output.next.coordinator ≠ .dagger := by
        intro hdagger
        have hfinalDagger :=
          (ReferenceActivePhysicalHorizon.Connected.coordinator_dagger htail hdagger).1
        exact hordinary hfinalDagger
      have hrecordInvariant :
          ReferenceUpDecoderBankInvariant.upBankInvariant record.input.state :=
        hinvariant record (by simp)
      have hpreparedOrdinary :
          (ReferenceActivePhysicalStep.prepare record.input).observeCoordinator.configuration ≠
            .dagger := by
        have h := hsuccessorOrdinary
        rw [record.output_eq] at h
        rw [(ReferenceActivePhysicalStep.step_next_fields record.input).1] at h
        exact h
      have hstep := observeCoordinator_replay (ReferenceActivePhysicalStep.prepare record.input)
        hrecordInvariant hpreparedOrdinary
      have hstepReplay :
          (ReferenceActivePhysicalStep.step record.input).next.upDecoderBank =
            replayOption initial.upDecoderBank
              (ReferenceActivePhysicalStep.step record.input).coordinator.up := by
        simpa [ReferenceActivePhysicalStep.step, hinput] using hstep.1
      have hbankOutput : record.output.next.upDecoderBank =
          (ReferenceActivePhysicalStep.step record.input).next.upDecoderBank :=
        congrArg (fun output : ReferenceActivePhysicalStep.RoundOutput record.input =>
          output.next.upDecoderBank) record.output_eq
      have hcoordinatorOutput : record.output.coordinator.up =
          (ReferenceActivePhysicalStep.step record.input).coordinator.up :=
        congrArg (fun output : ReferenceActivePhysicalStep.RoundOutput record.input =>
          output.coordinator.up) record.output_eq
      rw [← hcoordinatorOutput] at hstepReplay
      have hrecordReplay : record.output.next.upDecoderBank =
          replayRecord initial.upDecoderBank record := by
        calc
          record.output.next.upDecoderBank =
              (ReferenceActivePhysicalStep.step record.input).next.upDecoderBank := hbankOutput
          _ = replayOption initial.upDecoderBank record.output.coordinator.up := hstepReplay
          _ = replayRecord initial.upDecoderBank record := by
            cases hdiagnostic : record.output.coordinator.up <;>
              simp [replayOption, replayRecord, hdiagnostic]
      have hinvariantTail : ∀ current, current ∈ records →
          ReferenceUpDecoderBankInvariant.upBankInvariant current.input.state := by
        intro current hcurrent
        exact hinvariant current (by simp [hcurrent])
      have htailReplay := ih htail hinvariantTail
      calc
        final.upDecoderBank = records.foldl replayRecord record.output.next.upDecoderBank :=
          htailReplay
        _ = records.foldl replayRecord (replayRecord initial.upDecoderBank record) := by
          rw [hrecordReplay]
        _ = (record :: records).foldl replayRecord initial.upDecoderBank := rfl
/-- Ordinary endpoints force all physical record successors to be ordinary. -/
private theorem connected_record_successors_ordinary
    {initial final : ReferenceActivePhysicalStep.State p rate}
    {records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))}
    (hchain : ReferenceActivePhysicalHorizon.Connected initial records final)
    (hordinary : final.coordinator ≠ .dagger) :
    ∀ record, record ∈ records → record.output.next.coordinator ≠ .dagger := by
  induction records generalizing initial with
  | nil =>
      simp only [ReferenceActivePhysicalHorizon.Connected] at hchain
      subst final
      intro record hrecord
      simp at hrecord
  | cons record records ih =>
      simp only [ReferenceActivePhysicalHorizon.Connected] at hchain
      rcases hchain with ⟨_, htail⟩
      have hsuccessorOrdinary : record.output.next.coordinator ≠ .dagger := by
        intro hdagger
        have hfinalDagger :=
          (ReferenceActivePhysicalHorizon.Connected.coordinator_dagger htail hdagger).1
        exact hordinary hfinalDagger
      intro current hcurrent
      simp only [List.mem_cons] at hcurrent
      rcases hcurrent with rfl | hcurrent
      · exact hsuccessorOrdinary
      · exact ih htail current hcurrent
/-- Connected prefixes append the literal positive entries to collected history. -/
theorem connected_collected_upPositiveEntries
    {initial final : ReferenceActivePhysicalStep.State p rate}
    {records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))}
    (hchain : ReferenceActivePhysicalHorizon.Connected initial records final)
    (hinvariant : ∀ record, record ∈ records →
      ReferenceUpDecoderBankInvariant.upBankInvariant record.input.state)
    (hordinary : final.coordinator ≠ .dagger)
    (i : Fin (p.m - 1)) :
    AffineBatchDecoder.collected (final.upDecoderBank i) =
      AffineBatchDecoder.collected (initial.upDecoderBank i) ++
        retainedUpPositiveEntries records i := by
  induction records generalizing initial with
  | nil =>
      simp only [ReferenceActivePhysicalHorizon.Connected] at hchain
      subst final
      simp [retainedUpPositiveEntries]
  | cons record records ih =>
      simp only [ReferenceActivePhysicalHorizon.Connected] at hchain
      rcases hchain with ⟨hinput, htail⟩
      have hsuccessorOrdinary : record.output.next.coordinator ≠ .dagger := by
        intro hdagger
        have hfinalDagger :=
          (ReferenceActivePhysicalHorizon.Connected.coordinator_dagger htail hdagger).1
        exact hordinary hfinalDagger
      have hrecordInvariant := hinvariant record (by simp)
      have hhead := ordinaryRecord_collected_upPositiveEntries record hrecordInvariant
        hsuccessorOrdinary i
      have hhead' :
          AffineBatchDecoder.collected (record.output.next.upDecoderBank i) =
            AffineBatchDecoder.collected (initial.upDecoderBank i) ++
              recordUpPositiveEntries record i := by
        simpa [hinput] using hhead
      have hinvariantTail : ∀ current, current ∈ records →
          ReferenceUpDecoderBankInvariant.upBankInvariant current.input.state := by
        intro current hcurrent
        exact hinvariant current (by simp [hcurrent])
      have htailCollected := ih htail hinvariantTail
      calc
        AffineBatchDecoder.collected (final.upDecoderBank i) =
            AffineBatchDecoder.collected (record.output.next.upDecoderBank i) ++
              retainedUpPositiveEntries records i := htailCollected
        _ = (AffineBatchDecoder.collected (initial.upDecoderBank i) ++
              recordUpPositiveEntries record i) ++
              retainedUpPositiveEntries records i := by rw [hhead']
        _ = AffineBatchDecoder.collected (initial.upDecoderBank i) ++
              retainedUpPositiveEntries (record :: records) i := by
          simp [retainedUpPositiveEntries]
/-- The whole run equals replay of retained calls, given one initial invariant
and an explicit ordinary endpoint. -/
theorem run_upDecoderBank_replay
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p)
    (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hinitial : ReferenceUpDecoderBankInvariant.upBankInvariant initial)
    (hordinary : (ReferenceActivePhysicalHorizon.run initial rows selected rewards
      start count hspan hmode).finalState.coordinator ≠ .dagger) :
    (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count hspan hmode).finalState.upDecoderBank =
      replay initial.upDecoderBank
        (retainedUpDiagnostics (ReferenceActivePhysicalHorizon.run initial rows selected rewards
          start count hspan hmode).records) := by
  let execution := ReferenceActivePhysicalHorizon.run initial rows selected rewards
    start count hspan hmode
  have hinvariant : ∀ record, record ∈ execution.records →
      ReferenceUpDecoderBankInvariant.upBankInvariant record.input.state := by
    intro record hrecord
    exact ReferenceUpDecoderBankInvariant.run_record_input_upBankInvariant initial rows selected
      rewards start count hspan hmode hinitial record hrecord
  have hfold := connected_replay_fold execution.connected hinvariant hordinary
  rw [replay_records_eq_fold]
  exact hfold
/-- Retained call times match the exact run calendar, including empty runs. -/
theorem run_retainedUpCallTimes_calendar
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p)
    (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hinitial : ReferenceUpDecoderBankInvariant.upBankInvariant initial)
    (hordinary : (ReferenceActivePhysicalHorizon.run initial rows selected rewards
      start count hspan hmode).finalState.coordinator ≠ .dagger) :
    retainedUpCallTimes
        (ReferenceActivePhysicalHorizon.run initial rows selected rewards
          start count hspan hmode).records =
      physicalUpCalendarTimes
        (ReferenceActivePhysicalHorizon.run initial rows selected rewards
          start count hspan hmode).records ∧
      ((ReferenceActivePhysicalHorizon.run initial rows selected rewards
        start count hspan hmode).records.map
          (fun record => record.input.time.val)) =
        ReferenceActivePhysicalHorizon.calendar start count := by
  let execution := ReferenceActivePhysicalHorizon.run initial rows selected rewards
    start count hspan hmode
  have hinvariant : ∀ record, record ∈ execution.records →
      ReferenceUpDecoderBankInvariant.upBankInvariant record.input.state := by
    intro record hrecord
    exact ReferenceUpDecoderBankInvariant.run_record_input_upBankInvariant initial rows selected
      rewards start count hspan hmode hinitial record hrecord
  have hordinaryRecords := connected_record_successors_ordinary execution.connected hordinary
  constructor
  · exact retainedUpCallTimes_eq_physicalUpCalendarTimes execution.records hinvariant
      hordinaryRecords
  · exact ReferenceActivePhysicalHorizon.run_time_values initial rows selected rewards
      start count hspan hmode
/-- Collected state is its seed followed by positive saved calls. -/
theorem run_collected_upPositiveEntries
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p)
    (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hinitial : ReferenceUpDecoderBankInvariant.upBankInvariant initial)
    (hordinary : (ReferenceActivePhysicalHorizon.run initial rows selected rewards
      start count hspan hmode).finalState.coordinator ≠ .dagger)
    (i : Fin (p.m - 1)) :
    AffineBatchDecoder.collected
        ((ReferenceActivePhysicalHorizon.run initial rows selected rewards
          start count hspan hmode).finalState.upDecoderBank i) =
      AffineBatchDecoder.collected (initial.upDecoderBank i) ++
        retainedUpPositiveEntries
          (ReferenceActivePhysicalHorizon.run initial rows selected rewards
            start count hspan hmode).records i := by
  let execution := ReferenceActivePhysicalHorizon.run initial rows selected rewards
    start count hspan hmode
  have hinvariant : ∀ record, record ∈ execution.records →
      ReferenceUpDecoderBankInvariant.upBankInvariant record.input.state := by
    intro record hrecord
    exact ReferenceUpDecoderBankInvariant.run_record_input_upBankInvariant initial rows selected
      rewards start count hspan hmode hinitial record hrecord
  exact connected_collected_upPositiveEntries execution.connected hinvariant hordinary i
/-- New positive entries are chronological and lie in the run interval. -/
theorem run_upPositiveEntries_chronology
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p)
    (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hinitial : ReferenceUpDecoderBankInvariant.upBankInvariant initial)
    (hordinary : (ReferenceActivePhysicalHorizon.run initial rows selected rewards
      start count hspan hmode).finalState.coordinator ≠ .dagger)
    (i : Fin (p.m - 1)) :
    (retainedUpPositiveEntries
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards
        start count hspan hmode).records i).Pairwise
        (fun earlier later => earlier.time.val < later.time.val) ∧
      (∀ entry, entry ∈ retainedUpPositiveEntries
        (ReferenceActivePhysicalHorizon.run initial rows selected rewards
          start count hspan hmode).records i →
        start ≤ entry.time.val ∧ entry.time.val < start + count) := by
  let execution := ReferenceActivePhysicalHorizon.run initial rows selected rewards
    start count hspan hmode
  have hinvariant : ∀ record, record ∈ execution.records →
      ReferenceUpDecoderBankInvariant.upBankInvariant record.input.state := by
    intro record hrecord
    exact ReferenceUpDecoderBankInvariant.run_record_input_upBankInvariant initial rows selected
      rewards start count hspan hmode hinitial record hrecord
  have hordinaryRecords := connected_record_successors_ordinary execution.connected hordinary
  have hpositiveTimes := retainedUpPositiveEntries_time_map execution.records
    hinvariant hordinaryRecords i
  have hcalendarRecords :
      execution.records.map (fun record => record.input.time.val) =
        ReferenceActivePhysicalHorizon.calendar start count := by
    simpa [execution] using ReferenceActivePhysicalHorizon.run_time_values initial rows selected
      rewards start count hspan hmode
  have hcalendarPairwise :
      (ReferenceActivePhysicalHorizon.calendar start count).Pairwise (· < ·) := by
    simpa [ReferenceActivePhysicalHorizon.calendar] using
      (List.pairwise_lt_range' (s := start) (n := count) (step := 1) (by decide : 0 < 1))
  have htimePairwise :
      (execution.records.map (fun record => record.input.time.val)).Pairwise (· < ·) := by
    rw [hcalendarRecords]
    exact hcalendarPairwise
  have hrecordPairwise : execution.records.Pairwise
      (fun earlier later => earlier.input.time.val < later.input.time.val) :=
    List.pairwise_map.mp htimePairwise
  have hpositiveTimePairwise := retainedUpPositiveTimes_pairwise execution.records
    hrecordPairwise i
  constructor
  · have hentryTimePairwise :
        ((retainedUpPositiveEntries execution.records i).map
          (fun entry => entry.time.val)).Pairwise (· < ·) := by
      rw [hpositiveTimes]
      exact hpositiveTimePairwise
    exact List.pairwise_map.mp hentryTimePairwise
  · intro entry hentry
    have htimeMem : entry.time.val ∈ retainedUpPositiveTimes execution.records i := by
      rw [← hpositiveTimes]
      exact List.mem_map.mpr ⟨entry, hentry, rfl⟩
    obtain ⟨record, hrecord, hpositiveTime⟩ := List.mem_filterMap.mp htimeMem
    have hstamp := recordUpPositiveTime_eq_recordTime record i entry.time.val hpositiveTime
    have hcalendarMem := ReferenceUpDecoderBankInvariant.run_record_time_mem_calendar
      initial rows selected rewards start count hspan hmode record hrecord
    have hrange : record.input.time.val ∈ List.range' start count 1 := by
      simpa [ReferenceActivePhysicalHorizon.calendar] using hcalendarMem
    obtain ⟨offset, hoffset, hrecordTime⟩ := List.mem_range'.mp hrange
    have hentryTime : entry.time.val = start + offset := by
      calc
        entry.time.val = record.input.time.val := hstamp
        _ = start + 1 * offset := hrecordTime
        _ = start + offset := by omega
    constructor <;> omega
/-- Replay at the actual launched boundary with original binders preserved. -/
theorem ofActualLaunchedBoundary_run_upDecoderBank_replay
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (rate : ActualInitializationLaunchState.RateInput p) (C_star C_h : ℝ)
    (b : ReferenceInitializationRun.Boundary p)
    (h : b.completed < BootstrapDimensions.n_boot p)
    (actual : ActualInitializationRun.BlockCarry p rate
      (ReferenceInitializationRun.nextBlock b h))
    (past : List (ActualInitializationRun.PhysicalRoundRecord p rate source rewards))
    (hr : ActualReferenceInitializationBlock.BlockStartRelated source rewards C_star C_h rate
      (ReferenceInitializationRun.nextBlock b h) actual b past)
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
    (hordinary : (ReferenceActivePhysicalHorizon.run
      (ActualInitializationLaunchState.ofActualLaunchedBoundary source rewards rate C_star C_h
        b h actual past hr hdown hclean hforce launch learnerSeed hlaunched)
      source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start count
      hspan (by
        intro i
        have hactivation := ActualInitializationLaunchState.ofActualLaunchedBoundary_activation_le_blockStop
          source rewards rate C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed
          hlaunched i
        omega)).finalState.coordinator ≠ .dagger) :
    (let initial := ActualInitializationLaunchState.ofActualLaunchedBoundary source rewards rate
      C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed hlaunched;
    let hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start := by
      intro i
      have hactivation := ActualInitializationLaunchState.ofActualLaunchedBoundary_activation_le_blockStop
        source rewards rate C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed
        hlaunched i
      have hactivation' : (initial.activations i).val ≤
          BootstrapObservedFollower.blockStop p (ReferenceInitializationRun.nextBlock b h) + 1 := by
        simpa [initial] using hactivation
      omega;
    let execution := ReferenceActivePhysicalHorizon.run initial source.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start count hspan hmode;
    execution.finalState.upDecoderBank =
      replay initial.upDecoderBank (retainedUpDiagnostics execution.records) ∧
      (∀ i, AffineBatchDecoder.collected (execution.finalState.upDecoderBank i) =
        retainedUpPositiveEntries execution.records i)) := by
  let initial := ActualInitializationLaunchState.ofActualLaunchedBoundary source rewards rate
    C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed hlaunched
  let hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start := by
    intro i
    have hactivation := ActualInitializationLaunchState.ofActualLaunchedBoundary_activation_le_blockStop
      source rewards rate C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed
      hlaunched i
    have hactivation' : (initial.activations i).val ≤
        BootstrapObservedFollower.blockStop p (ReferenceInitializationRun.nextBlock b h) + 1 := by
      simpa [initial] using hactivation
    omega
  have hordinary' :
      (ReferenceActivePhysicalHorizon.run initial source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start count hspan
        hmode).finalState.coordinator ≠ .dagger := by
    simpa [initial, hmode] using hordinary
  have hinitial := ReferenceUpDecoderBankInvariant.ofActualLaunchedBoundary_upBankInvariant
    source rewards rate C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed
    hlaunched
  have hreplay := run_upDecoderBank_replay initial source.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start count hspan hmode
    hinitial hordinary'
  have hcollected := run_collected_upPositiveEntries initial source.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start count hspan hmode
    hinitial hordinary'
  have hinitialBank := ActualInitializationLaunchState.ofActualLaunchedBoundary_upDecoderBank
    source rewards rate C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed hlaunched
  refine ⟨hreplay, ?_⟩
  intro i
  have hseed : AffineBatchDecoder.collected (initial.upDecoderBank i) = [] := by
    rw [show initial.upDecoderBank = CoordinatorUpReception.initialUpDecoderBank p by
      simpa [initial] using hinitialBank]
    simp [CoordinatorUpReception.initialUpDecoderBank, AffineBatchDecoder.initial,
      AffineBatchDecoder.collected]
  have hresult := hcollected i
  rw [hseed] at hresult
  simpa using hresult
/-- At an actual cutoff record aligned with a computed prefix boundary, the
pre-reception bank is exactly the replayed prefix bank. `run_append` exposes
the remaining physical suffix; U supplies pending emptiness at the cutoff,
while completed history is preserved by the prefix replay. The state-link and
calendar-coordinate premises remain explicit, and this says nothing about the
post-reception cutoff bank. -/
theorem actualCutoff_prefix_upDecoderBank_replay
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p)
    (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start left right : ℕ) (hspan : start + (left + right) ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hinitial : ReferenceUpDecoderBankInvariant.upBankInvariant initial)
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hrecord : record ∈ (ReferenceActivePhysicalHorizon.run initial rows selected rewards
      start (left + right) hspan hmode).records)
    (hcut : ReferenceUpDecoderBankInvariant.isActualCutoffChosen
      record.output.preparation.coordinator)
    (htime : record.input.time.val = start + left)
    (hprefix : record.input.state =
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start left
        (by omega) hmode).finalState) :
    (let preRun := ReferenceActivePhysicalHorizon.run initial rows selected rewards start left
      (by omega) hmode;
    let fullRun := ReferenceActivePhysicalHorizon.run initial rows selected rewards start
      (left + right) hspan hmode;
    record.input.time.val < start + (left + right) ∧
      fullRun = ReferenceActivePhysicalHorizon.foldCalendar initial rows selected rewards start
        (start + left) right (by omega) (by omega) hmode preRun ∧
      record.input.state.upDecoderBank =
        replay initial.upDecoderBank (retainedUpDiagnostics preRun.records) ∧
      (∀ i, (record.input.state.upDecoderBank i).pending = []) ∧
      (∀ i, AffineBatchDecoder.collected (record.input.state.upDecoderBank i) =
        AffineBatchDecoder.collected (initial.upDecoderBank i) ++
          retainedUpPositiveEntries preRun.records i)) := by
  let preRun := ReferenceActivePhysicalHorizon.run initial rows selected rewards start left
    (by omega) hmode
  let fullRun := ReferenceActivePhysicalHorizon.run initial rows selected rewards start
    (left + right) hspan hmode
  have hcut' := hcut
  rw [record.output_eq] at hcut'
  change ReferenceUpDecoderBankInvariant.isActualCutoffChosen
    (ReferenceActivePhysicalStep.dispatch record.input) at hcut'
  rcases hcut' with ⟨registers, owned, base, outcome, hstate, _, _⟩
  have hrecordOrdinary : record.input.state.coordinator ≠ .dagger := by
    rw [hstate]
    simp
  have hprefixOrdinary : preRun.finalState.coordinator ≠ .dagger := by
    intro hdagger
    rw [← hprefix] at hdagger
    exact hrecordOrdinary hdagger
  have hcutCalendar := ReferenceUpDecoderBankInvariant.run_record_time_mem_calendar
    initial rows selected rewards start (left + right) hspan hmode record hrecord
  have hcutRange : record.input.time.val ∈
      List.range' start (left + right) 1 := by
    simpa [ReferenceActivePhysicalHorizon.calendar] using hcutCalendar
  obtain ⟨offset, hoffset, htime'⟩ := List.mem_range'.mp hcutRange
  have hright : 0 < right := by omega
  have happend := ReferenceActivePhysicalHorizon.run_append initial rows selected rewards
    start left right hspan hmode
  have happend' : fullRun = ReferenceActivePhysicalHorizon.foldCalendar initial rows
      selected rewards start (start + left) right (by omega) (by omega) hmode preRun := by
    simpa [fullRun, preRun] using happend
  have hbank := run_upDecoderBank_replay initial rows selected rewards start left (by omega)
    hmode hinitial (by simpa [preRun] using hprefixOrdinary)
  have hcollected := run_collected_upPositiveEntries initial rows selected rewards start left
    (by omega) hmode hinitial (by simpa [preRun] using hprefixOrdinary)
  have hpending := ReferenceUpDecoderBankInvariant.run_cutoff_up_pending_empty initial rows
    selected rewards start (left + right) hspan hmode hinitial record hrecord hcut
  refine ⟨by omega, happend', ?_, ?_, ?_⟩
  · rw [hprefix]
    exact hbank
  · exact hpending
  · intro i
    rw [hprefix]
    exact hcollected i

end Bandits.Support.ReferenceCoordinatorUpDecoderReplay

end
