/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCutoffRecordedService
public import Bandits.Support.ReferenceFirstLiveFollowerSafety
public import Bandits.Support.ReferenceGeneratedActivePrefixFactor

import Lean.Elab.Tactic.Omega
import Mathlib.Data.List.TakeWhile

/-!
# The actual first-cutoff UP receiver domain

Sources: `sources/zip4/manuscript/07_public_setup.tex:127-164`,
`sources/zip4/manuscript/05_binary_transport.tex:23-42`,
`sources/zip4/manuscript/06_interruptions.tex:41-44,246-258,277-285,327-344`,
and `sources/zip4/manuscript/appendix_a_local_protocol.tex:8-14,28-60`.

From the original initialization source, complete rows, selected private row,
and full reward table, this module follows the generated corrected launch
through the original active physical run to its actual first cutoff. It then
consumes the recorded-service producer's stage-(1) ledger and derives the
literal UP receiver's checked rejection and carried decoder-bank update. It
does not assert a post-reception finish, coordinator survival, or manuscript
lemma closure.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceFixedTimeSourceControlCoupling
open Bandits.Support.ReferenceInitializationControlRemainder
open Bandits.Support.ReferenceInitializationRun
open Bandits.Support.ReferenceGeneratedActivePrefixFactor
open Bandits.Support.ReferenceFirstLiveConfirmationHistory
open Bandits.Support.ReferenceFirstCutoffRecordedService
open Bandits.Support.ReferenceFirstLiveCoordinatorSafety
open Bandits.Support.CoordinatorUpReception
open Bandits.Support.CoordinatorCollectionLedger
open Bandits.Support.ReferenceUpReception
open scoped Classical

namespace Bandits.Support.ReferenceFirstCutoffReceiverDomain

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceGeneratedActivePrefixFactor.RateInput
abbrev SourceInput := BootstrapPrivateRoundStreams.SourceInput

variable {p : Parameters} {rate : RateInput p}

private theorem initial_decoder_step (input : CoordinatorUpReception.ReceptionInput p
    rate.eta.val rate.eta.property (ReferenceUpReception.sourceCap_forLedger rate)
    rate.n rate.n_scale) (hquota : 1 < AffineBatchDecoder.quota p)
    (hinitial : input.upDecoderBank input.selectedFollower = AffineBatchDecoder.initial p) :
    CoordinatorUpReception.decoderTransition input =
      (⟨if CoordinatorUpReception.receptionGate input ∧
          0 < input.ownObservation.val then
            [AffineBatchDecoder.entry p (CoordinatorUpReception.traceAt input) input.time]
          else [], []⟩, none) := by
  classical
  unfold CoordinatorUpReception.decoderTransition
  rw [hinitial]
  have hquotaPos : 0 < AffineBatchDecoder.quota p := by omega
  have hrounded : 0 < CoordinatorUpReception.roundedObservationValue p input.ownObservation ↔
      0 < input.ownObservation.val := by
    change 0 < (input.ownObservation.val : ℝ) / (ConstructorDimensions.D p : ℝ) ↔ _
    have hD : (ConstructorDimensions.D p : ℝ) > 0 := by
      exact_mod_cast ConstructorDimensions.D_pos p
    constructor
    · intro h
      by_contra hpositive
      have hzero : input.ownObservation.val = 0 := by omega
      simp [hzero] at h
    · intro h
      exact div_pos (by exact_mod_cast h) hD
  have hgateBool := CoordinatorUpReception.roundInput_selected_iff_gate input
  by_cases hgate : CoordinatorUpReception.receptionGate input
  · have hselected : (CoordinatorUpReception.roundInput input).selected = true :=
      hgateBool.mpr hgate
    by_cases hpositive : 0 < input.ownObservation.val
    · have heligible : AffineBatchDecoder.eligible
          (CoordinatorUpReception.roundInput input) :=
        ⟨hselected, rfl, hrounded.mpr hpositive⟩
      simp [AffineBatchDecoder.decodeStep, AffineBatchDecoder.step,
        AffineBatchDecoder.stepOutput, AffineBatchDecoder.positiveAt,
        CoordinatorUpReception.traceAt, heligible, hquota, hgate, hpositive,
        AffineBatchDecoder.initial]
    · have hnot : ¬ AffineBatchDecoder.eligible
          (CoordinatorUpReception.roundInput input) := by
        rintro ⟨_, _, hreward⟩
        have hrewardObs :
            0 < CoordinatorUpReception.roundedObservationValue p input.ownObservation := by
          simpa [CoordinatorUpReception.roundInput] using hreward
        exact hpositive (hrounded.mp hrewardObs)
      simp [AffineBatchDecoder.decodeStep, AffineBatchDecoder.step,
        AffineBatchDecoder.stepOutput, AffineBatchDecoder.positiveAt,
        CoordinatorUpReception.traceAt, hnot, hquotaPos, hgate, hpositive,
        AffineBatchDecoder.initial]
  · have hnot : ¬ AffineBatchDecoder.eligible
        (CoordinatorUpReception.roundInput input) := by
      rintro ⟨hselected, _, _⟩
      exact hgate (hgateBool.mp hselected)
    simp [AffineBatchDecoder.decodeStep, AffineBatchDecoder.step,
      AffineBatchDecoder.stepOutput, AffineBatchDecoder.positiveAt,
      CoordinatorUpReception.traceAt, hnot, hquotaPos, hgate,
      AffineBatchDecoder.initial]

private theorem quota_gt_one (p : Parameters) :
    1 < AffineBatchDecoder.quota p := by
  rw [CoordinatorUpReception.quota_eq_source]
  have hTD : 0 < p.T * ConstructorDimensions.D p :=
    Nat.mul_pos (ConstructorDimensions.T_pos p) (ConstructorDimensions.D_pos p)
  have hwidth : 0 < OrdinaryMessageCodec.fieldWidth p.T (ConstructorDimensions.D p) := by
    rw [OrdinaryMessageCodec.fieldWidth]
    exact Nat.clog_pos (by decide) (by omega)
  omega

private theorem connected_append_split
    {initial final : ReferenceActivePhysicalHorizon.State p rate}
    (left right : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (connected : ReferenceActivePhysicalHorizon.Connected initial (left ++ right) final) :
    ∃ middle,
      ReferenceActivePhysicalHorizon.Connected initial left middle ∧
      ReferenceActivePhysicalHorizon.Connected middle right final := by
  induction left generalizing initial with
  | nil =>
      simp only [List.nil_append] at connected
      exact ⟨initial, rfl, connected⟩
  | cons head tail ih =>
      simp only [List.cons_append,
        ReferenceActivePhysicalHorizon.Connected] at connected ⊢
      rcases connected with ⟨hinput, htail⟩
      obtain ⟨middle, hleft, hright⟩ := ih htail
      exact ⟨middle, ⟨hinput, hleft⟩, hright⟩

private theorem livePostChoice_bank {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ) (started : CoordinatorPhaseClock.StartRoundResult p) :
    (ReferenceActivePhysicalStep.livePostChoice prepared r q base started).upDecoderBank =
      x.state.upDecoderBank := by
  classical
  unfold ReferenceActivePhysicalStep.livePostChoice
  cases hrecording : CoordinatorRecorderComplementBridge.run
      (ReferenceActivePhysicalStep.liveRecordingInput prepared r started) with
  | none => simp [ReferenceActivePhysicalStep.coordinatorFailure]
  | some recording =>
      cases hservice : CoordinatorLiveServiceFinish.servicePass r q recording with
      | error reason =>
          simp [hservice, ReferenceActivePhysicalStep.coordinatorFailure]
      | ok serviced =>
          cases hconfirmation : CoordinatorLocalArmChoice.confirmationUpdate r.payload
              started.pending (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
              x.time x.row prepared.coordinatorObservation with
          | none =>
              simp [hservice, ReferenceActivePhysicalStep.coordinatorFailure]
          | some pending =>
              cases hfinish : CoordinatorPhaseClock.finishRound p rate.eta.val x.time
                  started.clock pending x.row with
              | error reason =>
                  simp [hservice, hfinish,
                    ReferenceActivePhysicalStep.coordinatorFailure]
              | ok finished =>
                  simp [hservice, hfinish]

private theorem collectionFinish_not_live
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (recording : CoordinatorRecordingOperation.Output p)
    (cut : ReferenceActivePhysicalStep.UpCut p rate)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ) :
    (ReferenceActivePhysicalStep.collectionFinish (x := x) payload started recording cut).configuration ≠
      .live r q base := by
  classical
  cases hresult : cut.result with
  | invalid => simp [ReferenceActivePhysicalStep.collectionFinish,
      ReferenceActivePhysicalStep.coordinatorFailure, hresult]
  | rejected output =>
      rcases output with ⟨ledger, bank⟩
      cases hfinish : CoordinatorCollectionLedger.finishRound ledger with
      | invalid => simp [ReferenceActivePhysicalStep.collectionFinish,
          ReferenceActivePhysicalStep.coordinatorFailure, hresult, hfinish]
      | rejected rejectedLedger =>
          simp [ReferenceActivePhysicalStep.collectionFinish,
            ReferenceActivePhysicalStep.coordinatorFailure, hresult, hfinish]
      | success ledgerFinished =>
          cases hclock : CoordinatorPhaseClock.finishRound p rate.eta.val x.time
              started.clock ledgerFinished.pending x.row with
          | error reason =>
              simp [ReferenceActivePhysicalStep.collectionFinish,
                ReferenceActivePhysicalStep.coordinatorFailure, hresult, hfinish, hclock]
          | ok clockFinished =>
              simp [ReferenceActivePhysicalStep.collectionFinish, hresult, hfinish, hclock]
  | success output =>
      rcases output with ⟨ledger, bank⟩
      cases hfinish : CoordinatorCollectionLedger.finishRound ledger with
      | invalid => simp [ReferenceActivePhysicalStep.collectionFinish,
          ReferenceActivePhysicalStep.coordinatorFailure, hresult, hfinish]
      | rejected rejectedLedger =>
          simp [ReferenceActivePhysicalStep.collectionFinish,
            ReferenceActivePhysicalStep.coordinatorFailure, hresult, hfinish]
      | success ledgerFinished =>
          cases hclock : CoordinatorPhaseClock.finishRound p rate.eta.val x.time
              started.clock ledgerFinished.pending x.row with
          | error reason =>
              simp [ReferenceActivePhysicalStep.collectionFinish,
                ReferenceActivePhysicalStep.coordinatorFailure, hresult, hfinish, hclock]
          | ok clockFinished =>
              simp [ReferenceActivePhysicalStep.collectionFinish,
                hresult, hfinish, hclock]

private theorem collectionPostChoice_not_live
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ) :
    (ReferenceActivePhysicalStep.collectionPostChoice prepared payload ledger started weights).configuration ≠
      .live r q base := by
  classical
  let recordingInput := ReferenceActivePhysicalStep.collectionRecordingInput
    prepared payload started weights
  cases hrecording : CoordinatorRecorderComplementBridge.run recordingInput with
  | none =>
      simp [ReferenceActivePhysicalStep.collectionPostChoice, recordingInput,
        hrecording, ReferenceActivePhysicalStep.coordinatorFailure]
  | some recording =>
      let enabled := ReferenceActivePhysicalStep.collectionEnabled ledger x.time
      let raw := CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording
      cases hstart : CoordinatorCollectionLedger.startRound ledger (x.time.val + 1)
          enabled raw with
      | invalid =>
          simp [ReferenceActivePhysicalStep.collectionPostChoice, recordingInput,
            hrecording, enabled, raw, hstart, ReferenceActivePhysicalStep.coordinatorFailure]
      | rejected rejectedLedger =>
          simp [ReferenceActivePhysicalStep.collectionPostChoice, recordingInput,
            hrecording, enabled, raw, hstart, ReferenceActivePhysicalStep.coordinatorFailure]
      | success ledgerStarted =>
          have hfinish := collectionFinish_not_live (x := x) payload started recording
            (ReferenceActivePhysicalStep.receiveUp prepared ledgerStarted) r q base
          simpa [ReferenceActivePhysicalStep.collectionPostChoice, recordingInput,
            hrecording, enabled, raw, hstart] using hfinish

private theorem successful_live_next_preserves_bank
    {record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)}
    {nextRegisters : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta}
    {nextOwned : CoordinatorLiveServiceFinish.OwnedRegisters nextRegisters}
    {nextBase : Fin (p.m - 1) → ℕ}
    (hnext : record.output.next.coordinator = .live nextRegisters nextOwned nextBase) :
    record.output.next.upDecoderBank = record.input.state.upDecoderBank := by
  let prepared := ReferenceActivePhysicalStep.prepare record.input
  have hobsLive : prepared.observeCoordinator.configuration =
      .live nextRegisters nextOwned nextBase := by
    rw [record.output_eq] at hnext
    calc
      prepared.observeCoordinator.configuration =
          (ReferenceActivePhysicalStep.step record.input).next.coordinator :=
        (ReferenceActivePhysicalStep.step_next_fields record.input).1.symm
      _ = .live nextRegisters nextOwned nextBase := hnext
  have hbank : prepared.observeCoordinator.upDecoderBank = record.input.state.upDecoderBank := by
    cases hcut : prepared.coordinator with
    | first outcome =>
        have heq := ReferenceActivePhysicalStep.observeCoordinator_first_equation
          prepared outcome hcut
        cases outcome with
        | chosen installed selection =>
            by_cases hnone : (ReferenceActivePhysicalStep.DispatchCut.first
                (.chosen installed selection)).selection = none
            · simp [heq, hnone, ReferenceActivePhysicalStep.coordinatorFailure] at hobsLive
            · rw [heq, ite_eq_right hnone]
              exact livePostChoice_bank prepared installed.registers
                installed.ownedRegisters installed.followerBaseScore
                installed.startRoundResult
        | choiceDomainFailure _ | recorderBoundaryFailure _ | choiceRejected _ =>
            simp [heq, ReferenceActivePhysicalStep.coordinatorFailure] at hobsLive
    | live registers owned base outcome =>
        have heq := ReferenceActivePhysicalStep.observeCoordinator_live_equation
          prepared registers owned base outcome hcut
        cases outcome with
        | clockFailure _ _ | initializerFailure _ _ _ _ | localFailure _ _ _ =>
            simp [heq, ReferenceActivePhysicalStep.coordinatorFailure] at hobsLive
        | continuingChosen dispatched startRoundEq continuation selection =>
            by_cases hnone : (ReferenceActivePhysicalStep.DispatchCut.live
                registers owned base (.continuingChosen dispatched startRoundEq
                  continuation selection)).selection = none
            · simp [heq, hnone, ReferenceActivePhysicalStep.coordinatorFailure] at hobsLive
            · rw [heq, ite_eq_right hnone]
              exact livePostChoice_bank prepared
                (ReferenceActivePhysicalStep.liveRegistersAt registers record.input.time)
                (ReferenceActivePhysicalStep.liveOwnedAt registers owned record.input.time)
                base dispatched.startResult
        | cutoffChosen dispatched startRoundEq ledger hinit hledger hdomain hclock hpending hnoassign selection =>
            by_cases hnone : (ReferenceActivePhysicalStep.DispatchCut.live
                registers owned base (.cutoffChosen dispatched startRoundEq ledger hinit hledger
                  hdomain hclock hpending hnoassign selection)).selection = none
            · simp [heq, hnone, ReferenceActivePhysicalStep.coordinatorFailure] at hobsLive
            · have hnotLive := collectionPostChoice_not_live prepared registers.payload
                (ReferenceActivePhysicalStep.sharedLedger ledger) dispatched.startResult
                (ReferenceActivePhysicalStep.liveRegistersAt registers record.input.time).complementWeights
                nextRegisters nextOwned nextBase
              exact False.elim (hnotLive (by simpa [heq, hnone] using hobsLive))
    | collection payload ledger clock cutoff outcome =>
        have heq := ReferenceActivePhysicalStep.observeCoordinator_collection_equation
          prepared payload ledger clock cutoff outcome hcut
        cases outcome with
        | clockFailure _ _ | localFailure _ _ _ _ | coreFailure _ _ _ _ =>
            simp [heq, ReferenceActivePhysicalStep.coordinatorFailure] at hobsLive
        | continuing core snapshot boundaryValid scoresChecked =>
            by_cases hnone : (ReferenceActivePhysicalStep.DispatchCut.collection
                payload ledger clock cutoff (.continuing core snapshot boundaryValid scoresChecked)).selection = none
            · simp [heq, hnone, ReferenceActivePhysicalStep.coordinatorFailure] at hobsLive
            · have hnotLive := collectionPostChoice_not_live prepared payload ledger
                snapshot.clockStarted
                (CoordinatorCollectionInteractive.PreObservationInputs.weights
                  (ReferenceActivePhysicalStep.collectionInput record.input payload ledger clock cutoff)
                  snapshot.inputsValid.ledger_valid snapshot.inputsValid.assignment_eq)
                nextRegisters nextOwned nextBase
              exact False.elim (hnotLive (by simpa [heq, hnone] using hobsLive))
        | laterReconstructionFailure core consistent started startRoundEq instruction
            assignmentStartEq reason laterEq =>
              simp [heq, ReferenceActivePhysicalStep.coordinatorFailure] at hobsLive
        | laterPrefixFailure core consistent started startRoundEq instruction
            assignmentStartEq arm reason laterEq =>
              simp [heq, ReferenceActivePhysicalStep.coordinatorFailure] at hobsLive
        | laterOrientationFailure core consistent started startRoundEq instruction
            assignmentStartEq set laterEq =>
              simp [heq, ReferenceActivePhysicalStep.coordinatorFailure] at hobsLive
        | laterChoiceFailure core consistent started startRoundEq instruction
            assignmentStartEq output localConsistencyEq clockData installation reason =>
              simp [heq, ReferenceActivePhysicalStep.coordinatorFailure] at hobsLive
        | laterChosen core consistent started startRoundEq instruction assignmentStartEq
            output localConsistencyEq clockData installed selection =>
            by_cases hnone : (ReferenceActivePhysicalStep.DispatchCut.collection
                payload ledger clock cutoff (.laterChosen core consistent started startRoundEq
                  instruction assignmentStartEq output localConsistencyEq clockData installed
                  selection)).selection = none
            · simp [heq, hnone, ReferenceActivePhysicalStep.coordinatorFailure] at hobsLive
            · rw [heq, ite_eq_right hnone]
              exact livePostChoice_bank prepared installed.registers installed.ownedRegisters
                installed.retainedBaseScore started
    | invalidCollectionCutoff =>
        have hfalse : False := by
          simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
            hcut, ReferenceActivePhysicalStep.coordinatorFailure] at hobsLive
        exact False.elim hfalse
    | dagger =>
        have hobs := ReferenceActivePhysicalStep.observeCoordinator_dagger prepared hcut
        have hfalse : False := by
          simp [hobs] at hobsLive
        exact False.elim hfalse
  rw [record.output_eq]
  exact (ReferenceActivePhysicalStep.step_next_fields record.input).2.1.trans hbank

private theorem connected_window_bank
    {initial final : ReferenceActivePhysicalHorizon.State p rate}
    (window suffix : List
      (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (hconnected : ReferenceActivePhysicalHorizon.Connected initial
      (window ++ suffix) final)
    (hsafe : ∀ k : Fin window.length,
      let record := window[k.val]
      record.output.coordinator.failure = none ∧
        ∃ recording, record.output.coordinator.recording = some recording ∧
          ∃ registers owned base,
            record.output.next.coordinator = .live registers owned base) :
    ∃ middle,
      ReferenceActivePhysicalHorizon.Connected initial window middle ∧
      ReferenceActivePhysicalHorizon.Connected middle suffix final ∧
      middle.upDecoderBank = initial.upDecoderBank := by
  induction window generalizing initial with
  | nil =>
      exact ⟨initial, rfl, hconnected, rfl⟩
  | cons head tail ih =>
      change head.input.state = initial ∧
        ReferenceActivePhysicalHorizon.Connected head.output.next (tail ++ suffix) final
        at hconnected
      rcases hconnected with ⟨hinput, htailConnected⟩
      have hheadSafe : head.output.coordinator.failure = none ∧
          ∃ recording, head.output.coordinator.recording = some recording ∧
            ∃ registers owned base,
              head.output.next.coordinator = .live registers owned base := by
        simpa using hsafe ⟨0, by simp⟩
      rcases hheadSafe with ⟨_, _, _, nextRegisters, nextOwned, nextBase, hnext⟩
      have hheadBank := successful_live_next_preserves_bank hnext
      have hsafeTail : ∀ k : Fin tail.length,
          let record := tail[k.val]
          record.output.coordinator.failure = none ∧
            ∃ recording, record.output.coordinator.recording = some recording ∧
              ∃ registers owned base,
                record.output.next.coordinator = .live registers owned base := by
        intro k
        let k' : Fin (head :: tail).length := ⟨k.val + 1, by simp⟩
        simpa [k'] using hsafe k'
      obtain ⟨middle, hprefix, hrest, hmiddleBank⟩ := ih htailConnected hsafeTail
      refine ⟨middle, ?_, hrest, ?_⟩
      · exact ⟨hinput, hprefix⟩
      · calc
          middle.upDecoderBank = head.output.next.upDecoderBank := hmiddleBank
          _ = head.input.state.upDecoderBank := hheadBank
          _ = initial.upDecoderBank := congrArg
            ReferenceActivePhysicalStep.State.upDecoderBank hinput

private theorem startRound_success_valid
    (ledger : CoordinatorCollectionLedger.Ledger p rate.eta.val rate.eta.property
      (ReferenceUpReception.sourceCap_forLedger rate) rate.n rate.n_scale)
    (time : ℕ) (enabled : Bool) (raw : Option (Fin p.K × ℕ))
    (next : CoordinatorCollectionLedger.Ledger p rate.eta.val rate.eta.property
      (ReferenceUpReception.sourceCap_forLedger rate) rate.n rate.n_scale)
    (hsuccess : CoordinatorCollectionLedger.startRound ledger time enabled raw =
      .success next) :
    CoordinatorCollectionLedger.validLedgerCheck next = true := by
  classical
  by_cases hinput : CoordinatorCollectionLedger.validLedgerCheck ledger = true ∧
      ledger.phase = .ready ∧ time = ledger.cursor ∧ 1 ≤ time ∧ time ≤ p.T ∧
        CoordinatorCollectionLedger.rawInputDomainCheck raw = true
  · rcases hinput with ⟨hledger, hphase, htime, hlow, hhigh, hraw⟩
    rw [htime] at hsuccess
    have hlow' : 1 ≤ ledger.cursor := by omega
    have hhigh' : ledger.cursor ≤ p.T := by omega
    let r : Fin p.T := ⟨ledger.cursor - 1, by omega⟩
    by_cases hfresh : CoordinatorCollectionLedger.rawSlotFreshCheck ledger r raw = true
    · let candidate := CoordinatorCollectionLedger.startRoundCandidate ledger r enabled raw
      by_cases hvalid : CoordinatorCollectionLedger.validLedgerCheck candidate = true
      · have heq : CoordinatorCollectionLedger.startRound ledger ledger.cursor enabled raw =
            .success candidate := by
          simp [CoordinatorCollectionLedger.startRound, hledger, hphase, hlow', hhigh',
            hraw, r, hfresh, candidate, hvalid]
        have hnext : candidate = next :=
          CoordinatorCollectionLedger.Checked.success.inj (heq.symm.trans hsuccess)
        rw [← hnext]
        exact hvalid
      · simp [CoordinatorCollectionLedger.startRound, hledger, hphase, hlow', hhigh',
          hraw, r, hfresh, candidate, hvalid] at hsuccess
    · simp [CoordinatorCollectionLedger.startRound, hledger, hphase, hlow', hhigh',
        hraw, r, hfresh] at hsuccess
  · simp [CoordinatorCollectionLedger.startRound, hinput] at hsuccess

private theorem actual_first_cutoff_receiver
    (initial : ReferenceActivePhysicalHorizon.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (J : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hfirst : initial.coordinator = .first)
    (hinitialBank : initial.upDecoderBank =
      CoordinatorUpReception.initialUpDecoderBank p)
    (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceActivePhysicalHorizon.run initial rows J rewards start count hspan active).records).length
        < count) :
    ∃ cut suffix,
      (ReferenceActivePhysicalHorizon.run initial rows J rewards start count hspan active).records =
        ReferenceFirstLiveConfirmationHistory.firstLiveWindow
          (ReferenceActivePhysicalHorizon.run initial rows J rewards start count hspan active).records ++
          cut :: suffix ∧
      cut.input.time.val = start +
        (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
          (ReferenceActivePhysicalHorizon.run initial rows J rewards start count hspan active).records).length ∧
      ∃ r q base,
        cut.input.state.coordinator = .live r q base ∧
      ∃ dispatched hstart ledger hinit hledger hdomain hclock hpending hnoAssignment selected,
        cut.output.preparation.coordinator = .live r q base
          (.cutoffChosen dispatched hstart ledger hinit hledger hdomain hclock hpending
            hnoAssignment selected) ∧
      ∃ recording,
        ReferenceCoordinatorRecorderCallTrace.actualBranchInput cut =
          some (CoordinatorRecorderComplementBridge.recorderInput
            (ReferenceActivePhysicalStep.collectionRecordingInput
              cut.output.preparation
              (ReferenceActivePhysicalStep.liveInput cut.input r q base).registers.payload
              dispatched.startResult
              (ReferenceActivePhysicalStep.liveInput cut.input r q base).registers.complementWeights)) ∧
        ReferenceCoordinatorRecorderCallTrace.recording
          (ReferenceActiveHorizonMeasurability.roundRecordCode cut) = some recording ∧
        cut.coordinatorDiagnostics.recording = some recording ∧
        CoordinatorRecordingOperation.run
          (CoordinatorRecorderComplementBridge.recorderInput
            (ReferenceActivePhysicalStep.collectionRecordingInput
              cut.output.preparation
              (ReferenceActivePhysicalStep.liveInput cut.input r q base).registers.payload
              dispatched.startResult
              (ReferenceActivePhysicalStep.liveInput cut.input r q base).registers.complementWeights)) =
          some recording ∧
        ∃ l1,
          CoordinatorCollectionLedger.startRound
            (ReferenceActivePhysicalStep.sharedLedger ledger) (cut.input.time.val + 1)
            (ReferenceActivePhysicalStep.collectionEnabled
              (ReferenceActivePhysicalStep.sharedLedger ledger) cut.input.time)
            (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) =
              .success l1 ∧
          l1 = CoordinatorCollectionLedger.startRoundCandidate
            (ReferenceActivePhysicalStep.sharedLedger ledger) cut.input.time
            (ReferenceActivePhysicalStep.collectionEnabled
              (ReferenceActivePhysicalStep.sharedLedger ledger) cut.input.time)
            (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) ∧
          ∃ input,
            input = ReferenceUpReception.receptionInputAtRow rate cut.input.row
              (ReferenceActivePhysicalStep.upInputs cut.output.preparation l1) cut.input.time ∧
            CoordinatorUpReception.receptionInputDomain input ∧
            CoordinatorUpReception.receptionInputCheck input = true ∧
            CoordinatorUpReception.decoderTransition input =
              (⟨if CoordinatorUpReception.receptionGate input ∧
                  0 < input.ownObservation.val then
                    [AffineBatchDecoder.entry p (CoordinatorUpReception.traceAt input) input.time]
                  else [], []⟩, none) ∧
            AffineBatchDecoder.quota p > 1 ∧
            ReferenceUpReception.rawParsedOutput rate input = none ∧
            ReferenceUpReception.filterRawByExpected
              (CoordinatorUpReception.decoderTransition input).2
              (ReferenceActivePhysicalStep.upExpected cut.output.preparation) = none ∧
            CoordinatorUpReception.parseDecoderOutput (p := p) (eta := rate.eta.val)
              (ReferenceUpReception.filterRawByExpected
                (CoordinatorUpReception.decoderTransition input).2
                (ReferenceActivePhysicalStep.upExpected cut.output.preparation)) = none ∧
            (ReferenceActivePhysicalStep.receiveUp cut.output.preparation l1).result =
              .rejected ({input.ledger with phase := CoordinatorCollectionLedger.Phase.decoded},
                CoordinatorUpReception.decoderBankAfter input) ∧
            CoordinatorUpReception.decoderBankAfter input =
              Function.update input.upDecoderBank input.selectedFollower
                (CoordinatorUpReception.decoderTransition input).1 ∧
            (CoordinatorUpReception.decoderTransition input).1.completed = [] ∧
            (CoordinatorUpReception.decoderTransition input).1.pending =
              (if CoordinatorUpReception.receptionGate input ∧ 0 < input.ownObservation.val then
                [AffineBatchDecoder.entry p (CoordinatorUpReception.traceAt input) input.time]
              else []) ∧
            ∃ diagnostic,
              (ReferenceActivePhysicalStep.receiveUp cut.output.preparation l1).diagnostic =
                some diagnostic ∧
              diagnostic.input = input ∧
              diagnostic.expected = ReferenceActivePhysicalStep.upExpected cut.output.preparation ∧
              diagnostic.decoderAfter = (CoordinatorUpReception.decoderTransition input).1 ∧
              diagnostic.raw = none ∧ diagnostic.parsed = none ∧
              diagnostic.locallyAccepted = false ∧
              diagnostic.rawMatches = decide
                (none = ReferenceActivePhysicalStep.upExpected cut.output.preparation) ∧
              diagnostic.wrongUniqueAccepted = false ∧
              (∀ i, i ≠ input.selectedFollower →
                (CoordinatorUpReception.decoderBankAfter input) i = input.upDecoderBank i) ∧
              (∀ _hfreeze : l1.cutoff = (ReferenceActivePhysicalStep.sharedLedger ledger).freezeAt,
                ReferenceActivePhysicalStep.collectionEnabled
                  (ReferenceActivePhysicalStep.sharedLedger ledger) cut.input.time = false) := by
  classical
  let execution := ReferenceActivePhysicalHorizon.run initial rows J rewards start count hspan active
  let window := ReferenceFirstLiveConfirmationHistory.firstLiveWindow execution.records
  have hwindowShort : window.length < count := by
    simpa [execution, window] using hshort
  have hservice := ReferenceFirstCutoffRecordedService.run_first_cutoff_recorded_service
    initial rows J rewards start count hspan active hfirst hwindowShort
  rcases hservice with ⟨cut, suffix, hrecords, hcutIndex, hcutTime,
    r, q, base, hcutState, hprefixLive,
    dispatched, hstart, ledger, hinit, hledger, hdomain, hclock, hpending,
    hnoAssignment, selected, hbranch,
    recording, hbranchInput, htrace, hrecordedDiagnostic, hrecordingRun, htail⟩
  let shared := ReferenceActivePhysicalStep.sharedLedger ledger
  let raw := CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording
  let enabled := ReferenceActivePhysicalStep.collectionEnabled shared cut.input.time
  dsimp only [shared, raw, enabled] at htail
  rcases htail with ⟨l1, hstage1, hl1, _hcurrentQueues, _hunknownQueues,
    _hrawBuffer, _hotherBuffer, _hnumericBounds⟩
  have hsafety := ReferenceFirstLiveCoordinatorSafety.run_first_live_coordinator_safety
    initial rows J rewards start count hspan active hfirst
  have hsafe : ∀ k : Fin window.length,
      let record := window[k.val]
      record.output.coordinator.failure = none ∧
        ∃ recording, record.output.coordinator.recording = some recording ∧
          ∃ registers owned base,
            record.output.next.coordinator = .live registers owned base := by
    simpa [execution, window] using hsafety.1
  have hconnected := ReferenceActivePhysicalHorizon.run_connected
    initial rows J rewards start count hspan active
  rw [hrecords] at hconnected
  obtain ⟨middle, hwindowConnected, htailConnected, hmiddleBank⟩ :=
    connected_window_bank window (cut :: suffix) hconnected hsafe
  change cut.input.state = middle ∧
    ReferenceActivePhysicalHorizon.Connected cut.output.next suffix execution.finalState
    at htailConnected
  have hcutBank : cut.input.state.upDecoderBank = initial.upDecoderBank := by
    rw [htailConnected.1, hmiddleBank]
  have hcutCoordinator : cut.input.state.coordinator = .live r q base := by
    simpa [execution, window] using
      (congrArg ReferenceActivePhysicalStep.State.coordinator hcutState).trans hprefixLive
  have hincomingBank : cut.input.state.upDecoderBank =
      CoordinatorUpReception.initialUpDecoderBank p := hcutBank.trans hinitialBank
  let prepared := cut.output.preparation
  let inputs := ReferenceActivePhysicalStep.upInputs prepared l1
  let input := ReferenceUpReception.receptionInputAtRow rate cut.input.row inputs cut.input.time
  have hsharedSigma : shared.sigma =
      (ReferenceActivePhysicalStep.liveInput cut.input r q base).registers.payload.sigma.val + 1 := by
    change ledger.sigma = _
    rw [hledger]
    rfl
  have hsharedCutoff : shared.cutoff = cut.input.time.val + 1 := by
    change ledger.cutoff = _
    rw [hledger]
    rfl
  have hledgerValid : CoordinatorCollectionLedger.validLedgerCheck l1 = true :=
    startRound_success_valid shared (cut.input.time.val + 1) enabled raw l1 hstage1
  have hl1Sigma : 1 ≤ l1.sigma := by
    rw [hl1]
    simp only [CoordinatorCollectionLedger.startRoundCandidate]
    rw [hsharedSigma]
    omega
  have hl1Cutoff : 1 ≤ l1.cutoff := by
    rw [hl1]
    simp only [CoordinatorCollectionLedger.startRoundCandidate]
    rw [hsharedCutoff]
    omega
  have hl1Cursor : l1.cursor ≤ p.T := by
    rw [hl1]
    simp [CoordinatorCollectionLedger.startRoundCandidate,
      CoordinatorCollectionLedger.sourceRound]
  have hl1CutoffCursor : l1.cutoff ≤ l1.cursor := by
    rw [hl1]
    simp only [CoordinatorCollectionLedger.startRoundCandidate]
    rw [hsharedCutoff]
    rfl
  have hinputBank : input.upDecoderBank =
      CoordinatorUpReception.initialUpDecoderBank p := by
    change cut.input.state.upDecoderBank = CoordinatorUpReception.initialUpDecoderBank p
    exact hincomingBank
  have hdomainInput : CoordinatorUpReception.receptionInputDomain input := by
    have hbankCheck : CoordinatorUpReception.decoderBankCheck p input.upDecoderBank = true := by
      rw [hinputBank]
      exact CoordinatorUpReception.initialUpDecoderBank_check p
    change CoordinatorCollectionLedger.validLedgerCheck l1 = true ∧
      1 ≤ l1.sigma ∧
      l1.phase = CoordinatorCollectionLedger.Phase.started ∧
      1 ≤ l1.cutoff ∧
      l1.cutoff ≤ l1.cursor ∧
      l1.cursor ≤ p.T ∧
      l1.cursor = CoordinatorCollectionLedger.sourceRound cut.input.time ∧
      CoordinatorUpReception.decoderBankCheck p input.upDecoderBank = true
    refine ⟨hledgerValid, hl1Sigma, ?_, hl1Cutoff, hl1CutoffCursor, hl1Cursor, ?_, hbankCheck⟩
    · rw [hl1]
      rfl
    · rw [hl1]
      rfl
  have hparseNone : CoordinatorUpReception.parseDecoderOutput (p := p)
      (eta := rate.eta.val) none = none := by
    change OrdinaryMessageCodec.parseUp
      (CoordinatorCollectionLedger.codecParams p rate.eta.val) none = none
    rfl
  have hcheckInput := (CoordinatorUpReception.receptionInputCheck_eq_true_iff input).2 hdomainInput
  have hselectedBank : input.upDecoderBank input.selectedFollower =
      AffineBatchDecoder.initial p := by
    rw [hinputBank]
    rfl
  have htransition := initial_decoder_step input (quota_gt_one p) hselectedBank
  have hrawNone : (CoordinatorUpReception.decoderTransition input).2 = none :=
    congrArg Prod.snd htransition
  have hfilteredNone : ReferenceUpReception.filterRawByExpected
      (CoordinatorUpReception.decoderTransition input).2
      (ReferenceActivePhysicalStep.upExpected prepared) = none := by
    simp [hrawNone, ReferenceUpReception.filterRawByExpected]
  have hrawParsed : ReferenceUpReception.rawParsedOutput rate input = none := by
    change CoordinatorUpReception.parseDecoderOutput
      (CoordinatorUpReception.decoderTransition input).2 = none
    rw [hrawNone]
    exact hparseNone
  have hfilteredParsed : CoordinatorUpReception.parseDecoderOutput (p := p) (eta := rate.eta.val)
      (ReferenceUpReception.filterRawByExpected
        (CoordinatorUpReception.decoderTransition input).2
        (ReferenceActivePhysicalStep.upExpected prepared)) = none := by
    rw [hfilteredNone]
    exact hparseNone
  have haccepted : ReferenceUpReception.rawParsedLocalAcceptance rate input = false := by
    simp [ReferenceUpReception.rawParsedLocalAcceptance, hrawParsed]
  have hwrong : ReferenceUpReception.wrongUniqueAndLocalAcceptanceAtRow rate
      cut.input.row inputs cut.input.time
      (prepared.followers.followers (ReferenceActivePhysicalStep.upSenderIndex cut.input))
      (prepared.follower_alignment _).1 (prepared.follower_alignment _).2.1
      (prepared.follower_alignment _).2.2.1 rfl = false := by
    simp [ReferenceUpReception.wrongUniqueAndLocalAcceptanceAtRow, input, hrawNone]
  have hdecoderBankSelected : input.upDecoderBank input.selectedFollower =
      AffineBatchDecoder.initial p := hselectedBank
  have htransitionState : (CoordinatorUpReception.decoderTransition input).1 =
      ⟨if CoordinatorUpReception.receptionGate input ∧ 0 < input.ownObservation.val then
          [AffineBatchDecoder.entry p (CoordinatorUpReception.traceAt input) input.time]
        else [], []⟩ := congrArg Prod.fst htransition
  have hreceive : (ReferenceActivePhysicalStep.receiveUp prepared l1).result =
      .rejected ({input.ledger with phase := CoordinatorCollectionLedger.Phase.decoded},
        CoordinatorUpReception.decoderBankAfter input) := by
    have hdomainAtRow : CoordinatorUpReception.receptionInputDomain
        (ReferenceUpReception.receptionInputAtRow rate cut.input.row inputs cut.input.time) := by
      simpa [input] using hdomainInput
    have hrawNoneAtRow :
        (CoordinatorUpReception.decoderTransition
          (ReferenceUpReception.receptionInputAtRow rate cut.input.row inputs cut.input.time)).2 = none := by
      simpa [input] using hrawNone
    have hdecodeAtRow := CoordinatorUpReception.decodeUp_none_rejected
      (ReferenceUpReception.receptionInputAtRow rate cut.input.row inputs cut.input.time)
      hdomainAtRow
    let sender := prepared.followers.followers
      (ReferenceActivePhysicalStep.upSenderIndex cut.input)
    let senderIndex := ReferenceActivePhysicalStep.upSenderIndex cut.input
    let senderRow := (prepared.follower_alignment senderIndex).1
    let senderFollower := (prepared.follower_alignment senderIndex).2.1
    have senderFollowerAtRow : sender.follower =
        (ReferenceUpReception.receptionInputAtRow rate cut.input.row inputs cut.input.time).selectedFollower := by
      calc
        sender.follower = senderIndex := senderFollower
        _ = (ReferenceUpReception.receptionInputAtRow rate cut.input.row inputs cut.input.time).selectedFollower := by
          simp [senderIndex, ReferenceActivePhysicalStep.upSenderIndex]
    let senderTime := (prepared.follower_alignment senderIndex).2.2.1
    have senderTimeAtRow : sender.time =
        (ReferenceUpReception.receptionInputAtRow rate cut.input.row inputs cut.input.time).time := by
      calc
        sender.time = cut.input.time := senderTime
        _ = (ReferenceUpReception.receptionInputAtRow rate cut.input.row inputs cut.input.time).time := by
          simp [ReferenceUpReception.receptionInputAtRow_inputTime, inputs,
            ReferenceActivePhysicalStep.upInputs, prepared]
    have hfilteredRawAtRow : ReferenceUpReception.filterRawByExpected
        (CoordinatorUpReception.decoderTransition
          (ReferenceUpReception.receptionInputAtRow rate cut.input.row inputs cut.input.time)).2
        (ReferenceUpReception.currentOfferWord rate cut.input.row
          (ReferenceUpReception.receptionInputAtRow rate cut.input.row inputs cut.input.time).selectedFollower
          (ReferenceUpReception.receptionInputAtRow rate cut.input.row inputs cut.input.time).time
          sender senderRow senderFollowerAtRow senderTimeAtRow) = none := by
      rw [hrawNoneAtRow]
      unfold ReferenceUpReception.filterRawByExpected
      split <;> rfl
    have hfiltered := ReferenceUpReception.receiveUpFilteredAtRow_eq_filtered_decode
      rate cut.input.row inputs cut.input.time
      sender
      senderRow senderFollowerAtRow senderTimeAtRow rfl hcheckInput
    change ReferenceUpReception.receiveUpFilteredAtRow rate cut.input.row inputs
      cut.input.time sender senderRow senderFollowerAtRow senderTimeAtRow rfl = _
    rw [hfiltered]
    rw [hfilteredRawAtRow]
    rw [hparseNone]
    rw [hdecodeAtRow]
    simp [CoordinatorUpReception.packDecodeResult, input, inputs, prepared]
  have hupDiagnostic : (ReferenceActivePhysicalStep.receiveUp prepared l1).diagnostic =
      some {
        input := input
        expected := ReferenceActivePhysicalStep.upExpected prepared
        decoderAfter := (CoordinatorUpReception.decoderTransition input).1
        raw := none
        parsed := none
        locallyAccepted := false
        rawMatches := decide (none = ReferenceActivePhysicalStep.upExpected prepared)
        wrongUniqueAccepted := false } := by
    simp [ReferenceActivePhysicalStep.receiveUp, prepared, inputs, input,
      hcheckInput, hrawNone, hrawParsed, haccepted, hwrong]
  have htransitionCompleted : (CoordinatorUpReception.decoderTransition input).1.completed = [] := by
    rw [htransitionState]
  have htransitionPending : (CoordinatorUpReception.decoderTransition input).1.pending =
      if CoordinatorUpReception.receptionGate input ∧ 0 < input.ownObservation.val then
        [AffineBatchDecoder.entry p (CoordinatorUpReception.traceAt input) input.time]
      else [] := by
    rw [htransitionState]
  have hfreezeDisabled : l1.cutoff = shared.freezeAt →
      ReferenceActivePhysicalStep.collectionEnabled shared cut.input.time = false := by
    intro hfreeze
    have hcutoff : l1.cutoff = shared.cutoff := by
      rw [hl1]
      rfl
    have htime : shared.cutoff = cut.input.time.val + 1 := hsharedCutoff
    have hfreezeAt : shared.freezeAt = cut.input.time.val + 1 := by
      calc
        shared.freezeAt = l1.cutoff := hfreeze.symm
        _ = shared.cutoff := hcutoff
        _ = cut.input.time.val + 1 := htime
    simp [ReferenceActivePhysicalStep.collectionEnabled, hfreezeAt]
  refine ⟨cut, suffix, hrecords, ?_, r, q, base, ?_, dispatched,
    hstart, ledger, hinit, hledger, hdomain, hclock, hpending, hnoAssignment,
    selected, ?_, recording, hbranchInput, htrace, hrecordedDiagnostic, hrecordingRun,
    l1, hstage1, hl1, input, rfl, hdomainInput, hcheckInput, htransition,
    quota_gt_one p, hrawParsed, hfilteredNone, hfilteredParsed, hreceive, rfl,
    htransitionCompleted, htransitionPending, ?_, ?_⟩
  · simpa [execution, window] using hcutTime
  · exact hcutCoordinator
  · exact hbranch
  · let diagnostic : ReferenceActivePhysicalStep.UpDiagnostic p rate := {
      input := input
      expected := ReferenceActivePhysicalStep.upExpected prepared
      decoderAfter := (CoordinatorUpReception.decoderTransition input).1
      raw := none
      parsed := none
      locallyAccepted := false
      rawMatches := decide (none = ReferenceActivePhysicalStep.upExpected prepared)
      wrongUniqueAccepted := false }
    exact diagnostic
  · let diagnostic : ReferenceActivePhysicalStep.UpDiagnostic p rate := {
      input := input
      expected := ReferenceActivePhysicalStep.upExpected prepared
      decoderAfter := (CoordinatorUpReception.decoderTransition input).1
      raw := none
      parsed := none
      locallyAccepted := false
      rawMatches := decide (none = ReferenceActivePhysicalStep.upExpected prepared)
      wrongUniqueAccepted := false }
    refine ⟨hupDiagnostic, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
    · intro i hi
      exact CoordinatorUpReception.decoderBankAfter_unselected input i hi
    · exact hfreezeDisabled

/-- The generated source-facing input to the actual first-cutoff receiver.
The launch event, elapsed start, control split, stratum, launch-start event,
corrected active seed, and incoming initial UP bank are all derived from the
original source. The sole extra run selector is the strict first-window
length bound. -/
theorem run_generated_first_cutoff_receiver_domain
    (rate : RateInput p) (z : SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true)
    (s : ℕ)
    (hsElapsed : s = ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed)
    (hsT : s < p.T)
    (count : ℕ) (hspan : s + count ≤ p.T)
    (t : Fin p.T) (ht : t.val = s) :
    let J := ActualInitializationPhysicalStep.selectedRowIndex p z
    let split := ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p J t z
    let hremainder : split.2 ∈
        ReferenceFixedTimeSourceControlCoupling.fixedControlRemainderStratum p J t := by
      change PrivateSourceStreams.coordinatorIndex p
        ((ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p J t z).2.2).1.2 = J
      rw [ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_private]
      change ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p z = J
      rw [ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex]
    let hstart : split.2 ∈ launchStartRemainderEvent rate rewards C_star C_h J t s split.1 := by
      exact (ReferenceInitializationControlRemainder.launchStartRemainderEvent_iff_source
        rate rewards C_star C_h J t split.1 z rfl s (Nat.le_of_eq ht.symm)).mpr
          ⟨hcross, hsElapsed.symm⟩
    let initial := ReferenceGeneratedActivePrefixFactor.generatedActiveSeed
      rate rewards C_star C_h J t split.1 split.2 hremainder s
      (Nat.le_of_eq ht.symm) hstart
    let active := (ReferenceGeneratedActivePrefixFactor.generatedActiveSeed_spec
      rate rewards C_star C_h J t split.1 split.2 hremainder s
      (Nat.le_of_eq ht.symm) hstart).2.1
    let execution := ReferenceActivePhysicalHorizon.run initial z.1.2 J rewards s count hspan active
    let window := ReferenceFirstLiveConfirmationHistory.firstLiveWindow execution.records
    split.2 ∈ ReferenceFixedTimeSourceControlCoupling.fixedControlRemainderStratum p J t ∧
    split.2 ∈ launchStartRemainderEvent rate rewards C_star C_h J t s split.1 ∧
      s < p.T ∧
      initial.coordinator = .first ∧
      initial.upDecoderBank = CoordinatorUpReception.initialUpDecoderBank p ∧
      (window.length < count →
        ∃ cut suffix,
          execution.records = window ++ cut :: suffix ∧
          cut.input.time.val = s + window.length ∧
          ∃ r q base,
            cut.input.state.coordinator = .live r q base ∧
          ∃ dispatched hstartCut ledger hinit hledger hdomain hclock hpending hnoAssignment selected,
            cut.output.preparation.coordinator = .live r q base
              (.cutoffChosen dispatched hstartCut ledger hinit hledger hdomain hclock hpending
                hnoAssignment selected) ∧
          ∃ recording,
            ReferenceCoordinatorRecorderCallTrace.actualBranchInput cut =
              some (CoordinatorRecorderComplementBridge.recorderInput
                (ReferenceActivePhysicalStep.collectionRecordingInput
                  cut.output.preparation
                  (ReferenceActivePhysicalStep.liveInput cut.input r q base).registers.payload
                  dispatched.startResult
                  (ReferenceActivePhysicalStep.liveInput cut.input r q base).registers.complementWeights)) ∧
            ReferenceCoordinatorRecorderCallTrace.recording
              (ReferenceActiveHorizonMeasurability.roundRecordCode cut) = some recording ∧
            cut.coordinatorDiagnostics.recording = some recording ∧
            CoordinatorRecordingOperation.run
              (CoordinatorRecorderComplementBridge.recorderInput
                (ReferenceActivePhysicalStep.collectionRecordingInput
                  cut.output.preparation
                  (ReferenceActivePhysicalStep.liveInput cut.input r q base).registers.payload
                  dispatched.startResult
                  (ReferenceActivePhysicalStep.liveInput cut.input r q base).registers.complementWeights)) =
              some recording ∧
            ∃ l1,
              CoordinatorCollectionLedger.startRound
                (ReferenceActivePhysicalStep.sharedLedger ledger) (cut.input.time.val + 1)
                (ReferenceActivePhysicalStep.collectionEnabled
                  (ReferenceActivePhysicalStep.sharedLedger ledger) cut.input.time)
                (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) =
                  .success l1 ∧
              l1 = CoordinatorCollectionLedger.startRoundCandidate
                (ReferenceActivePhysicalStep.sharedLedger ledger) cut.input.time
                (ReferenceActivePhysicalStep.collectionEnabled
                  (ReferenceActivePhysicalStep.sharedLedger ledger) cut.input.time)
                (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) ∧
              ∃ input,
                input = ReferenceUpReception.receptionInputAtRow rate cut.input.row
                  (ReferenceActivePhysicalStep.upInputs cut.output.preparation l1) cut.input.time ∧
                CoordinatorUpReception.receptionInputDomain input ∧
                CoordinatorUpReception.receptionInputCheck input = true ∧
                CoordinatorUpReception.decoderTransition input =
                  (⟨if CoordinatorUpReception.receptionGate input ∧
                      0 < input.ownObservation.val then
                        [AffineBatchDecoder.entry p (CoordinatorUpReception.traceAt input) input.time]
                      else [], []⟩, none) ∧
                AffineBatchDecoder.quota p > 1 ∧
                ReferenceUpReception.rawParsedOutput rate input = none ∧
                ReferenceUpReception.filterRawByExpected
                  (CoordinatorUpReception.decoderTransition input).2
                  (ReferenceActivePhysicalStep.upExpected cut.output.preparation) = none ∧
                CoordinatorUpReception.parseDecoderOutput (p := p) (eta := rate.eta.val)
                  (ReferenceUpReception.filterRawByExpected
                    (CoordinatorUpReception.decoderTransition input).2
                    (ReferenceActivePhysicalStep.upExpected cut.output.preparation)) = none ∧
                (ReferenceActivePhysicalStep.receiveUp cut.output.preparation l1).result =
                  .rejected ({input.ledger with phase := CoordinatorCollectionLedger.Phase.decoded},
                    CoordinatorUpReception.decoderBankAfter input) ∧
                CoordinatorUpReception.decoderBankAfter input =
                  Function.update input.upDecoderBank input.selectedFollower
                    (CoordinatorUpReception.decoderTransition input).1 ∧
                (CoordinatorUpReception.decoderTransition input).1.completed = [] ∧
                (CoordinatorUpReception.decoderTransition input).1.pending =
                  (if CoordinatorUpReception.receptionGate input ∧ 0 < input.ownObservation.val then
                    [AffineBatchDecoder.entry p (CoordinatorUpReception.traceAt input) input.time]
                  else []) ∧
                ∃ diagnostic,
                  (ReferenceActivePhysicalStep.receiveUp cut.output.preparation l1).diagnostic =
                    some diagnostic ∧
                  diagnostic.input = input ∧
                  diagnostic.expected = ReferenceActivePhysicalStep.upExpected cut.output.preparation ∧
                  diagnostic.decoderAfter = (CoordinatorUpReception.decoderTransition input).1 ∧
                  diagnostic.raw = none ∧ diagnostic.parsed = none ∧
                  diagnostic.locallyAccepted = false ∧
                  diagnostic.rawMatches = decide
                    (none = ReferenceActivePhysicalStep.upExpected cut.output.preparation) ∧
                  diagnostic.wrongUniqueAccepted = false ∧
                  (∀ i, i ≠ input.selectedFollower →
                    (CoordinatorUpReception.decoderBankAfter input) i = input.upDecoderBank i) ∧
                  (∀ _hfreeze : l1.cutoff =
                    (ReferenceActivePhysicalStep.sharedLedger ledger).freezeAt,
                    ReferenceActivePhysicalStep.collectionEnabled
                      (ReferenceActivePhysicalStep.sharedLedger ledger) cut.input.time = false)) := by
  classical
  let J := ActualInitializationPhysicalStep.selectedRowIndex p z
  let split := ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p J t z
  have hrem : split.2 ∈
      ReferenceFixedTimeSourceControlCoupling.fixedControlRemainderStratum p J t := by
    change PrivateSourceStreams.coordinatorIndex p
      ((ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p J t z).2.2).1.2 = J
    rw [ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_private]
    change ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p z = J
    rw [ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex]
  have hstart : split.2 ∈
      launchStartRemainderEvent rate rewards C_star C_h J t s split.1 := by
    exact (ReferenceInitializationControlRemainder.launchStartRemainderEvent_iff_source
      rate rewards C_star C_h J t split.1 z rfl s (Nat.le_of_eq ht.symm)).mpr
        ⟨hcross, hsElapsed.symm⟩
  let initial := ReferenceGeneratedActivePrefixFactor.generatedActiveSeed
    rate rewards C_star C_h J t split.1 split.2 hrem s
    (Nat.le_of_eq ht.symm) hstart
  have hspec := ReferenceGeneratedActivePrefixFactor.generatedActiveSeed_spec
    rate rewards C_star C_h J t split.1 split.2 hrem s
    (Nat.le_of_eq ht.symm) hstart
  have hsource : ReferenceGeneratedActivePrefixFactor.splitSource J t split.1 split.2 = z := by
    let e := ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p J t
    change e.symm (e z) = z
    exact e.symm_apply_apply z
  have hseedLaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch rate z rewards
      C_star C_h = some initial := by
    simpa [initial, hsource] using hspec.1
  obtain ⟨activeSeed, hlaunch, hcoord, hbank, _, _, _⟩ :=
    ReferenceCorrectedInitializationLaunch.correctedLaunch_coordinator_provenance
      rate z rewards C_star C_h hcross
  have hseedEq : initial = activeSeed := Option.some.inj (hseedLaunch.symm.trans hlaunch)
  have hfirst : initial.coordinator = .first := by
    rw [hseedEq]
    exact hcoord
  have hinitialBank : initial.upDecoderBank =
      CoordinatorUpReception.initialUpDecoderBank p := by
    rw [hseedEq]
    exact hbank
  let active := hspec.2.1
  let execution := ReferenceActivePhysicalHorizon.run initial z.1.2 J rewards s count hspan active
  let window := ReferenceFirstLiveConfirmationHistory.firstLiveWindow execution.records
  refine ⟨hrem, hstart, hsT, hfirst, hinitialBank, ?_⟩
  intro hshort
  exact actual_first_cutoff_receiver initial z.1.2 J rewards s count hspan
    active hfirst hinitialBank hshort

end Bandits.Support.ReferenceFirstCutoffReceiverDomain

end
