/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionCompletedPrefix
public import Bandits.Support.ReferenceFirstLaunchNumericalCell

/-!
# Whole-payload origin for first-collection DOWN diagnostics

Sources: `sources/zip4/manuscript/06_interruptions.tex:9-100,192-233,246-344`,
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-64`, and
`sources/zip4/manuscript/04_slow_fast_learner.tex:157-174`.

The producer keeps the original source telescope and the completed-prefix
diagnostics. It identifies the same actual first cutoff as the outside-register
initializer, produces its first installed payload, and traces every actual
selected payload in the raw collection window back to that birth. Receiver
queries remain conditional on actual retained diagnostics; this module asserts
no UP acceptance, successful extraction, or queue/score truth.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferenceCollectionPhaseHistory
open Bandits.Support.ReferenceFirstLiveConfirmationHistory
open Bandits.Support.ReferenceAssignmentPayloadPersistence
open Bandits.Support.ReferenceAssignmentPayloadChronology
open Bandits.Support.ReferenceSelectedPayloadChronology
open Bandits.Support.ReferenceFirstDownRecoveryBudget
open Bandits.Support.ReferenceFollowerSparseEmissionRecovery
open Bandits.Support.ReferenceAcceptedUpFollowerHistory
open Bandits.Support.ReferenceActiveDataOwnership
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.ActualInitializationPhysicalStep
open Bandits.Support.FollowerCutoffScan

namespace Bandits.Support.ReferenceFirstCollectionDownPayloadOrigin

variable {p : ConstructorDimensions.Parameters}

private theorem input_coordinator_first_of_prepared_first
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (outcome : CoordinatorRoundDispatch.FirstOutcome
      (ReferenceActivePhysicalStep.firstInput x))
    (hprepared : (ReferenceActivePhysicalStep.prepare x).coordinator = .first outcome) :
    x.state.coordinator = .first := by
  have hdispatch : ReferenceActivePhysicalStep.dispatch x = .first outcome := by
    calc
      ReferenceActivePhysicalStep.dispatch x =
          (ReferenceActivePhysicalStep.prepare x).coordinator :=
        (ReferenceActivePhysicalStep.prepare x).coordinator_eq.symm
      _ = .first outcome := hprepared
  cases hstate : x.state.coordinator with
  | first => rfl
  | live registers owned base =>
      cases hrun : CoordinatorRoundDispatch.dispatch
          (.live (ReferenceActivePhysicalStep.liveInput x registers owned base)) with
      | live actual =>
          have hcut : ReferenceActivePhysicalStep.dispatch x =
              .live registers owned base actual := by
            simp [ReferenceActivePhysicalStep.dispatch, hstate, hrun]
            rfl
          rw [hcut] at hdispatch
          cases hdispatch
  | collection payload ledger proposal =>
      by_cases hvalid : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
      · let cutoff : Fin p.T := ⟨ledger.cutoff - 1, by omega⟩
        let clock := ReferenceActivePhysicalStep.collectionClock payload ledger proposal cutoff
        cases hrun : CoordinatorRoundDispatch.dispatch
            (.collection (ReferenceActivePhysicalStep.collectionInput x payload ledger clock cutoff)) with
        | collection actual =>
            have hcut : ReferenceActivePhysicalStep.dispatch x =
                .collection payload ledger clock cutoff actual := by
              simp [ReferenceActivePhysicalStep.dispatch, hstate, hvalid, cutoff, clock, hrun]
              rfl
            rw [hcut] at hdispatch
            cases hdispatch
      · have hcut : ReferenceActivePhysicalStep.dispatch x = .invalidCollectionCutoff := by
          simp [ReferenceActivePhysicalStep.dispatch, hstate, hvalid]
        rw [hcut] at hdispatch
        cases hdispatch
  | dagger =>
      have hcut : ReferenceActivePhysicalStep.dispatch x = .dagger := by
        simp [ReferenceActivePhysicalStep.dispatch, hstate]
      rw [hcut] at hdispatch
      cases hdispatch

private theorem livePostChoice_configuration_ne_first
    {rate : ReferenceActivePhysicalStep.RateInput p}
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
    (base : Fin (p.m - 1) → ℕ) (started : CoordinatorPhaseClock.StartRoundResult p) :
    (ReferenceActivePhysicalStep.livePostChoice prepared registers owned base started).configuration ≠
      .first := by
  unfold ReferenceActivePhysicalStep.livePostChoice
  cases hrecord : CoordinatorRecorderComplementBridge.run
      (ReferenceActivePhysicalStep.liveRecordingInput prepared registers started) with
  | none => simp [ReferenceActivePhysicalStep.coordinatorFailure]
  | some recording =>
      cases hservice : CoordinatorLiveServiceFinish.servicePass registers owned recording with
      | error reason => simp [hservice, ReferenceActivePhysicalStep.coordinatorFailure]
      | ok serviced =>
          cases hconfirmation : CoordinatorLocalArmChoice.confirmationUpdate registers.payload
              started.pending (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
              x.time x.row prepared.coordinatorObservation with
          | none => simp [hservice, ReferenceActivePhysicalStep.coordinatorFailure]
          | some pending =>
              cases hfinish : CoordinatorPhaseClock.finishRound p rate.eta.val x.time
                  started.clock pending x.row with
              | error reason => simp [hservice, hfinish,
                  ReferenceActivePhysicalStep.coordinatorFailure]
              | ok finished => simp [hservice, hfinish]

private theorem collectionFinish_configuration_ne_first
    {rate : ReferenceActivePhysicalStep.RateInput p}
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (recording : CoordinatorRecordingOperation.Output p)
    (cut : ReferenceActivePhysicalStep.UpCut p rate) :
    (ReferenceActivePhysicalStep.collectionFinish (x := x) payload started recording cut).configuration ≠
      .first := by
  unfold ReferenceActivePhysicalStep.collectionFinish
  cases hresult : cut.result with
  | invalid => simp [ReferenceActivePhysicalStep.coordinatorFailure]
  | success pair =>
      rcases pair with ⟨ledger, bank⟩
      cases hledger : CoordinatorCollectionLedger.finishRound ledger with
      | invalid => simp [hledger, ReferenceActivePhysicalStep.coordinatorFailure]
      | rejected rejected => simp [hledger, ReferenceActivePhysicalStep.coordinatorFailure]
      | success finishedLedger =>
          cases hclock : CoordinatorPhaseClock.finishRound p rate.eta.val x.time
              started.clock finishedLedger.pending x.row with
          | error reason => simp [hledger, hclock, ReferenceActivePhysicalStep.coordinatorFailure]
          | ok finishedClock => simp [hledger, hclock]
  | rejected pair =>
      rcases pair with ⟨ledger, bank⟩
      cases hledger : CoordinatorCollectionLedger.finishRound ledger with
      | invalid => simp [hledger, ReferenceActivePhysicalStep.coordinatorFailure]
      | rejected rejected => simp [hledger, ReferenceActivePhysicalStep.coordinatorFailure]
      | success finishedLedger =>
          cases hclock : CoordinatorPhaseClock.finishRound p rate.eta.val x.time
              started.clock finishedLedger.pending x.row with
          | error reason => simp [hledger, hclock, ReferenceActivePhysicalStep.coordinatorFailure]
          | ok finishedClock => simp [hledger, hclock]

private theorem collectionPostChoice_configuration_ne_first
    {rate : ReferenceActivePhysicalStep.RateInput p}
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ) :
    (ReferenceActivePhysicalStep.collectionPostChoice prepared payload ledger started weights).configuration ≠
      .first := by
  unfold ReferenceActivePhysicalStep.collectionPostChoice
  cases hrecord : CoordinatorRecorderComplementBridge.run
      (ReferenceActivePhysicalStep.collectionRecordingInput prepared payload started weights) with
  | none => simp [ReferenceActivePhysicalStep.coordinatorFailure]
  | some recording =>
      cases hstart : CoordinatorCollectionLedger.startRound ledger (x.time.val + 1)
          (ReferenceActivePhysicalStep.collectionEnabled ledger x.time)
          (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) with
      | invalid => simp [hstart, ReferenceActivePhysicalStep.coordinatorFailure]
      | rejected rejected => simp [hstart, ReferenceActivePhysicalStep.coordinatorFailure]
      | success startedLedger =>
          simpa [hrecord, hstart] using
            (collectionFinish_configuration_ne_first (x := x) payload started recording
              (ReferenceActivePhysicalStep.receiveUp prepared startedLedger))

/-- Every actual operation successor has left the distinguished first state,
including failures after the coordinator has already exposed its choice. -/
private theorem step_coordinator_ne_first
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (x : ReferenceActivePhysicalStep.RoundInput p rate) :
    (ReferenceActivePhysicalStep.step x).next.coordinator ≠ .first := by
  rw [(ReferenceActivePhysicalStep.step_next_fields x).1]
  cases hcoord : (ReferenceActivePhysicalStep.prepare x).coordinator with
  | dagger =>
      simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
        ReferenceActivePhysicalStep.DispatchCut.selection, hcoord]
  | first outcome =>
      have hobserve := ReferenceActivePhysicalStep.observeCoordinator_first_equation
        (ReferenceActivePhysicalStep.prepare x) outcome hcoord
      by_cases hnone : (ReferenceActivePhysicalStep.DispatchCut.first outcome).selection = none
      · rw [hobserve, ite_eq_left hnone]
        simp [ReferenceActivePhysicalStep.coordinatorFailure]
      · rw [hobserve, ite_eq_right hnone]
        cases outcome with
        | chosen installed choice =>
            exact livePostChoice_configuration_ne_first
              (ReferenceActivePhysicalStep.prepare x) installed.registers installed.ownedRegisters
              installed.followerBaseScore installed.startRoundResult
        | _ => simp [ReferenceActivePhysicalStep.DispatchCut.selection] at hnone
  | live registers owned base outcome =>
      have hobserve := ReferenceActivePhysicalStep.observeCoordinator_live_equation
        (ReferenceActivePhysicalStep.prepare x) registers owned base outcome hcoord
      by_cases hnone : (ReferenceActivePhysicalStep.DispatchCut.live registers owned base outcome).selection = none
      · rw [hobserve, ite_eq_left hnone]
        simp [ReferenceActivePhysicalStep.coordinatorFailure]
      · rw [hobserve, ite_eq_right hnone]
        cases outcome with
        | continuingChosen dispatched startRound continuation choice =>
            exact livePostChoice_configuration_ne_first
              (ReferenceActivePhysicalStep.prepare x)
              (ReferenceActivePhysicalStep.liveRegistersAt registers x.time)
              (ReferenceActivePhysicalStep.liveOwnedAt registers owned x.time) base dispatched.startResult
        | cutoffChosen dispatched startRound ledger initialization ledgerCandidate domain clock pending noAssignment choice =>
            exact collectionPostChoice_configuration_ne_first
              (ReferenceActivePhysicalStep.prepare x) registers.payload
              (ReferenceActivePhysicalStep.sharedLedger ledger) dispatched.startResult
              (ReferenceActivePhysicalStep.liveRegistersAt registers x.time).complementWeights
        | _ => simp [ReferenceActivePhysicalStep.DispatchCut.selection] at hnone
  | collection payload ledger clock cutoff outcome =>
      have hobserve := ReferenceActivePhysicalStep.observeCoordinator_collection_equation
        (ReferenceActivePhysicalStep.prepare x) payload ledger clock cutoff outcome hcoord
      by_cases hnone : (ReferenceActivePhysicalStep.DispatchCut.collection payload ledger clock cutoff outcome).selection = none
      · rw [hobserve, ite_eq_left hnone]
        simp [ReferenceActivePhysicalStep.coordinatorFailure]
      · rw [hobserve, ite_eq_right hnone]
        cases outcome with
        | continuing core prepared boundary currentScores =>
            exact collectionPostChoice_configuration_ne_first
              (ReferenceActivePhysicalStep.prepare x) payload ledger prepared.clockStarted
              (CoordinatorCollectionInteractive.PreObservationInputs.weights
                (ReferenceActivePhysicalStep.collectionInput x payload ledger clock cutoff)
                prepared.inputsValid.ledger_valid prepared.inputsValid.assignment_eq)
        | laterChosen core consistent started startRound instruction assignmentStart output consistency clockData installed choice =>
            exact livePostChoice_configuration_ne_first
              (ReferenceActivePhysicalStep.prepare x) installed.registers installed.ownedRegisters
              installed.retainedBaseScore started
        | _ => simp [ReferenceActivePhysicalStep.DispatchCut.selection] at hnone
  | invalidCollectionCutoff =>
      simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
        ReferenceActivePhysicalStep.DispatchCut.selection, hcoord,
        ReferenceActivePhysicalStep.coordinatorFailure]

private theorem run_final_coordinator_first_only
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hfirst : (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count
      hspan hmode).finalState.coordinator = .first) :
    count = 0 := by
  cases count with
  | zero => rfl
  | succ count =>
      have hlast := ReferenceAssignmentPayloadChronology.run_successor_finalState_eq_actualRunRecordAt
        initial rows selected rewards start count (by omega) hmode
      have hne : (ReferenceActivePhysicalHorizon.run initial rows selected rewards start
          (count + 1) (by omega) hmode).finalState.coordinator ≠ .first := by
        rw [hlast]
        have hstep := step_coordinator_ne_first
          (ReferenceAssignmentPayloadChronology.actualRunRecordAt initial rows selected rewards
            start count (by omega) hmode).input
        simpa [ReferenceAssignmentPayloadChronology.actualRunRecordAt] using hstep
      exact False.elim (hne hfirst)

private theorem run_record_time_of_lookup
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (n : ℕ) (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hget : (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count
      hspan hmode).records[n]? = some record) :
    record.input.time.val = start + n := by
  have hmap : ((ReferenceActivePhysicalHorizon.run initial rows selected rewards start count
      hspan hmode).records.map fun r => r.input.time.val)[n]? =
        some record.input.time.val := by
    simp only [List.getElem?_map, hget, Option.map_some]
  rw [ReferenceActivePhysicalHorizon.run_time_values] at hmap
  have hn : n < count := by
    have hlen := List.getElem?_eq_some_iff.mp hget |>.1
    have hcount := ReferenceActivePhysicalHorizon.run_record_count
      initial rows selected rewards start count hspan hmode
    rw [hcount] at hlen
    exact hlen
  have hcalendar : (ReferenceActivePhysicalHorizon.calendar start count)[n]? =
      some (start + n) := by
    have hbound : n < (ReferenceActivePhysicalHorizon.calendar start count).length := by
      simpa [ReferenceActivePhysicalHorizon.calendar] using hn
    rw [List.getElem?_eq_getElem hbound]
    simp [ReferenceActivePhysicalHorizon.calendar]
  rw [hcalendar] at hmap
  exact (Option.some.inj hmap).symm

private theorem run_record_mem_index_time
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hmem : record ∈ (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count
      hspan hmode).records) :
    ∃ n, n < count ∧
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count hspan hmode).records[n]? =
        some record ∧
      record.input.time.val = start + n := by
  obtain ⟨n, hget⟩ := List.mem_iff_getElem?.mp hmem
  have hn : n < count := by
    have hbound := List.getElem?_eq_some_iff.mp hget |>.1
    have hcount := ReferenceActivePhysicalHorizon.run_record_count
      initial rows selected rewards start count hspan hmode
    rw [hcount] at hbound
    exact hbound
  have htime := run_record_time_of_lookup initial rows selected rewards start count hspan hmode n record
    hget
  exact ⟨n, hn, hget, htime⟩

private theorem run_record_input_ne_first_of_positive_offset
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hmem : record ∈ (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count
      hspan hmode).records)
    (offset : ℕ) (hoffset : 0 < offset)
    (htime : record.input.time.val = start + offset) :
    record.input.state.coordinator ≠ .first := by
  obtain ⟨prefixLength, hprefix, hprefixTime, hstate⟩ :=
    ReferenceSelectedPayloadChronology.actualRunRecord_has_prefix initial rows selected rewards
      start count hspan hmode record hmem
  have hprefixEq : prefixLength = offset := by omega
  subst prefixLength
  intro hrecordFirst
  have hrunFirst :
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start offset
        (by omega) hmode).finalState.coordinator = .first := by
    simpa [hstate] using hrecordFirst
  have hzero := run_final_coordinator_first_only initial rows selected rewards start offset
    (by omega) hmode hrunFirst
  omega

private theorem selectionAt_actual_choice
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (started : CoordinatorPhaseClock.StartRoundResult p) (time : Fin p.T)
    (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ)
    (choice : CoordinatorRoundDispatch.ArmSelection payload started time weights x.row)
    (htime : time = x.time) :
    ∃ selected : ReferenceActivePhysicalStep.Selection x,
      ReferenceActivePhysicalStep.selectionAt x payload started time weights choice = some selected ∧
        selected.view.payload = payload := by
  let selected : ReferenceActivePhysicalStep.Selection x := {
    view := {
      payload := payload
      pendingAtChoice := started.pending
      cutoff := CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u
      complementWeights := weights }
    started := started
    pending_eq := rfl
    cutoff_eq := rfl
    arm := choice.arm
    choice_eq := by simpa only [htime] using choice.armChoice_eq }
  refine ⟨selected, ?_, rfl⟩
  simp [ReferenceActivePhysicalStep.selectionAt, htime, selected]

private theorem selection_of_installation_birth
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (hbirth : ReferenceAssignmentPayloadPersistence.InstallationBirth record payload) :
    ∃ selected : ReferenceActivePhysicalStep.Selection record.input,
      record.output.preparation.coordinator.selection = some selected ∧
        selected.view.payload = payload := by
  cases hcoord : record.output.preparation.coordinator with
  | first outcome =>
      cases outcome with
      | chosen installed choice =>
          have hbirth' := hbirth
          simp [ReferenceAssignmentPayloadPersistence.InstallationBirth, hcoord] at hbirth'
          have hpayload : payload = installed.registers.payload := by
            exact hbirth'.1
          have hprepared : (ReferenceActivePhysicalStep.prepare record.input).coordinator =
              .first (.chosen installed choice) := by
            have h := hcoord
            rw [record.output_eq] at h
            simpa [ReferenceActivePhysicalStep.step] using h
          have hstate := input_coordinator_first_of_prepared_first record.input
            (.chosen installed choice) hprepared
          have hdispatch := ReferenceActivePhysicalStep.dispatch_first record.input hstate
          have hchosen : CoordinatorRoundDispatch.dispatchFirst
              (ReferenceActivePhysicalStep.firstInput record.input) = .chosen installed choice := by
            have heq := hdispatch.symm.trans hprepared
            injection heq with hchosen
          have htime := ReferenceActivePhysicalStep.dispatchFirst_chosen_time
            record.input installed choice hchosen
          obtain ⟨selected, hselectionAt, hviewPayload⟩ := selectionAt_actual_choice
            record.input installed.registers.payload installed.startRoundResult
            installed.registers.time installed.registers.complementWeights choice htime
          refine ⟨selected, ?_, ?_⟩
          · simpa only [ReferenceActivePhysicalStep.DispatchCut.selection] using hselectionAt
          · exact hviewPayload.trans hpayload.symm
      | _ => simp [ReferenceAssignmentPayloadPersistence.InstallationBirth, hcoord] at hbirth
  | collection payload' ledger clock cutoff outcome =>
      cases outcome with
      | laterChosen core consistent started hstart instruction hinstruction output outputConsistent clockData installed choice =>
          have hbirth' := hbirth
          simp [ReferenceAssignmentPayloadPersistence.InstallationBirth, hcoord] at hbirth'
          have hpayload : payload = installed.registers.payload := by
            exact hbirth'.1
          have htime := ReferenceActivePhysicalStep.later_instruction_time record.input
            payload' ledger clock cutoff core started instruction hstart hinstruction
          obtain ⟨selected, hselectionAt, hviewPayload⟩ := selectionAt_actual_choice
            record.input installed.registers.payload started instruction.time
            installed.registers.complementWeights choice htime
          refine ⟨selected, ?_, ?_⟩
          · simpa only [ReferenceActivePhysicalStep.DispatchCut.selection] using hselectionAt
          · exact hviewPayload.trans hpayload.symm
      | _ => simp [ReferenceAssignmentPayloadPersistence.InstallationBirth, hcoord] at hbirth
  | live _ _ _ _ => simp [ReferenceAssignmentPayloadPersistence.InstallationBirth, hcoord] at hbirth
  | invalidCollectionCutoff =>
      simp [ReferenceAssignmentPayloadPersistence.InstallationBirth, hcoord] at hbirth
  | dagger => simp [ReferenceAssignmentPayloadPersistence.InstallationBirth, hcoord] at hbirth

private theorem selection_of_equal_installation_birth
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (birth record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (heq : birth = record)
    (hbirth : ReferenceAssignmentPayloadPersistence.InstallationBirth birth payload) :
    ∃ selected : ReferenceActivePhysicalStep.Selection record.input,
      record.output.preparation.coordinator.selection = some selected ∧
        selected.view.payload = payload := by
  cases heq
  exact selection_of_installation_birth birth payload hbirth

private theorem selection_transport_of_equal_record
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (birth record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (selected : ReferenceActivePhysicalStep.Selection birth.input)
    (heq : birth = record)
    (hselected : birth.output.preparation.coordinator.selection = some selected) :
    ∃ selectedAtRecord : ReferenceActivePhysicalStep.Selection record.input,
      record.output.preparation.coordinator.selection = some selectedAtRecord ∧
        selectedAtRecord.view.payload = selected.view.payload := by
  cases heq
  exact ⟨selected, hselected, rfl⟩

private theorem laterChosen_false_of_mem_takeWhile
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (suffix : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hmem : record ∈ suffix.takeWhile
      (fun record => !ReferenceCollectionPhaseHistory.laterChosen record.input)) :
    ReferenceCollectionPhaseHistory.laterChosen record.input = false := by
  induction suffix generalizing record with
  | nil => simp at hmem
  | cons head tail ih =>
      by_cases hp : !ReferenceCollectionPhaseHistory.laterChosen head.input
      · simp [List.takeWhile, hp] at hmem
        rcases hmem with heq | hmem
        · subst record
          simpa using hp
        · exact ih record hmem
      · simp [List.takeWhile, hp] at hmem

private theorem laterChosen_false_of_collectionWindow_mem
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (w : ℕ) (cut : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (suffix : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (hwindow : ReferenceCollectionPhaseHistory.collectionWindow records w =
      cut :: suffix.takeWhile (fun record => !ReferenceCollectionPhaseHistory.laterChosen record.input))
    (hcutoff : ReferenceCollectionPhaseHistory.cutoffChosen cut.input = true)
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hmem : record ∈ ReferenceCollectionPhaseHistory.collectionWindow records w) :
    ReferenceCollectionPhaseHistory.laterChosen record.input = false := by
  rw [hwindow] at hmem
  rcases List.mem_cons.mp hmem with hcut | htail
  · subst record
    cases hcoord : (ReferenceActivePhysicalStep.prepare cut.input).coordinator with
    | live r q base outcome =>
        cases outcome <;>
          simp [ReferenceCollectionPhaseHistory.cutoffChosen,
            ReferenceCollectionPhaseHistory.laterChosen, hcoord] at hcutoff ⊢
    | _ => simp [ReferenceCollectionPhaseHistory.cutoffChosen, hcoord] at hcutoff
  · exact laterChosen_false_of_mem_takeWhile suffix record htail

private theorem run_records_prefix_mem
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start left right : ℕ) (hspan : start + (left + right) ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    {record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)}
    (hrecord : record ∈ (ReferenceActivePhysicalHorizon.run initial rows selected rewards start left
      (by omega) hmode).records) :
    record ∈ (ReferenceActivePhysicalHorizon.run initial rows selected rewards start (left + right)
      hspan hmode).records := by
  obtain ⟨suffix, hprefix⟩ := ReferenceCollectionPhaseHistory.run_records_prefix
    initial rows selected rewards start left right hspan hmode
  rw [hprefix]
  exact List.mem_append_left _ hrecord

/- The source-facing completed-prefix output, retained as one independent
field so the producer exposes the exact imported C telescope. -/
structure FirstCollectionDownPayloadOriginClaim
    (rate : ReferenceFirstCollectionEpochAlignment.RateInput p)
    (source : ReferenceFirstCollectionEpochAlignment.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (count : ℕ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (hspan : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed + count ≤ p.T)
    (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
        rate source rewards C_star C_h hcross count hspan).records).length < count)
    (s : ℕ)
    (I : ReferenceActivePhysicalStep.State p rate)
    (Erun : ReferenceActivePhysicalHorizon.Run I)
    (W : List (ReferenceFirstLiveConfirmationHistory.Record (p := p) (rate := rate)))
    (w : ℕ)
    (B : List (ReferenceCollectionPhaseHistory.Record (p := p) (rate := rate)))
    (u : ℕ) : Prop where
  completedPrefix :
    ∃ (cut : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
        (suffix : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
        (seg : ReferenceCollectionSegmentExtraction.Segment rate),
        Erun.records = W ++ cut :: suffix ∧
        seg.entry = cut ∧
        ReferenceCollectionSegmentExtraction.segmentAt Erun.records w = some seg ∧
        B = cut :: suffix.takeWhile
          (fun record => !ReferenceCollectionPhaseHistory.laterChosen record.input) ∧
        seg.records <+: B ∧
        seg.records = B.take seg.records.length ∧
        B = seg.records ++ B.drop seg.records.length ∧
        seg.records.length ≤ B.length ∧
        (∀ hlen : seg.records.length ≤ B.length, ∀ k : Fin seg.records.length,
          B[k.val]'(Nat.lt_of_lt_of_le k.isLt hlen) = seg.records[k.val] ∧
            Erun.records[w + k.val]? = some seg.records[k.val] ∧
            seg.records[k.val].input.time.val + 1 = u + k.val) ∧
        (∀ record ∈ seg.records, ∃ completed,
          ReferenceCollectionSegmentExtraction.extractRound record = some completed ∧
            completed.input.round = record.input.time) ∧
        seg.inputs.length = seg.records.length ∧
        seg.inputs.map (fun input => input.round.val + 1) =
          (List.range seg.records.length).map (fun k => u + k) ∧
        seg.remaining = B.drop seg.records.length ++ Erun.records.drop (w + B.length) ∧
        (ReferenceCollectionSegmentExtraction.extractRound cut = none →
          seg.records = [] ∧ seg.remaining = Erun.records.drop w) ∧
        match Erun.records.drop (w + B.length) with
        | [] => True
        | boundary :: _ =>
            Erun.records[w + B.length]? = some boundary ∧
              ReferenceCollectionPhaseHistory.laterChosen boundary.input = true
  origin :
    ∃ (cutoffRecord : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
      (P0 : ReferenceActivePhysicalStep.Payload rate)
      (birth : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
      (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
      (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
      (base : Fin (p.m - 1) → ℕ),
      (∃ hindex : w < Erun.records.length,
        cutoffRecord = Erun.records[w]'hindex) ∧
      (∀ cut suffix, Erun.records = W ++ cut :: suffix → cut = cutoffRecord) ∧
      cutoffRecord.input.state.coordinator = .live registers owned base ∧
      ReferenceCollectionPhaseHistory.cutoffChosen cutoffRecord.input = true ∧
      P0 = registers.payload ∧
      P0.sigma.val = s ∧
      (∀ a, P0.queues a = 0) ∧
      FollowerCutoffScan.firstCutoff p rate.eta.val P0.sigma
        (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
          (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source))) = u ∧
      birth ∈ Erun.records ∧
      ReferenceAssignmentPayloadPersistence.InstallationBirth birth P0 ∧
      birth.input.time.val = s ∧
      (∃ installed birthSelection,
        birth.output.preparation.coordinator = .first (.chosen installed birthSelection) ∧
          installed.registers.payload = P0) ∧
      (∀ (k : Fin B.length),
        Erun.records[w + k.val]? = some B[k.val] ∧
          B[k.val].input.time.val + 1 = u + k.val) ∧
      (∀ (k : Fin B.length)
        (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)),
        Erun.records[w + k.val]? = some record →
        ∀ (selected : ReferenceActivePhysicalStep.Selection record.input),
          record.output.preparation.coordinator.selection = some selected →
            selected.view.payload = P0) ∧
      (∀ (k : Fin B.length)
        (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)),
        Erun.records[w + k.val]? = some record →
        ∀ i (M : ReferenceAcceptedUpFollowerHistory.DownRecord (p := p) (rate := rate)),
          ReferenceAcceptedUpFollowerHistory.RetainedDown record i M →
            M = P0.downRecord i ∧ M.val.sigma = s + 1 ∧ M.val.q = 0) ∧
      (∀ (k : Fin B.length) (j : ℕ), j < w + k.val →
        ∀ (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)),
          Erun.records[j]? = some record →
            ∀ i (M : ReferenceAcceptedUpFollowerHistory.DownRecord (p := p) (rate := rate)),
              ReferenceAcceptedUpFollowerHistory.RetainedDown record i M →
                M = P0.downRecord i ∧ M.val.sigma = s + 1 ∧ M.val.q = 0)

/- The whole-payload origin for a first collection window over the same
complete source telescope used by the completed-prefix producer. Operation
queries are conclusions only when their actual selection or retained DOWN
diagnostic is present.

The `completedPrefix` field is the complete completed-prefix result, including the raw
window, cut, failed records, `seg.remaining`, and exit. The following
equalities identify that cut with the outside-initializer's exact cutoff
record; the payload and receiver conclusions are derived from the same run.
-/
theorem actual_first_collection_down_payload_origin
    (rate : ReferenceFirstCollectionEpochAlignment.RateInput p)
    (source : ReferenceFirstCollectionEpochAlignment.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (count : ℕ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (hspan : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed + count ≤ p.T)
    (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
        rate source rewards C_star C_h hcross count hspan).records).length < count) :
    let s := ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
    let I := ReferenceFirstCollectionEpochAlignment.actualLaunchState
      rate source rewards C_star C_h hcross
    let Erun := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
      rate source rewards C_star C_h hcross count hspan
    let W := ReferenceFirstLiveConfirmationHistory.firstLiveWindow Erun.records
    let w := W.length
    let B := ReferenceCollectionPhaseHistory.collectionWindow Erun.records w
    let u := s + w + 1
    FirstCollectionDownPayloadOriginClaim rate source rewards C_star C_h count
      hcross hspan hshort s I Erun W w B u := by
  let s := ReferenceInitializationRun.elapsed p
    (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
  let I := ReferenceFirstCollectionEpochAlignment.actualLaunchState
    rate source rewards C_star C_h hcross
  let Erun := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
    rate source rewards C_star C_h hcross count hspan
  let W := ReferenceFirstLiveConfirmationHistory.firstLiveWindow Erun.records
  let w := W.length
  let B := ReferenceCollectionPhaseHistory.collectionWindow Erun.records w
  let u := s + w + 1
  have hseed := ReferenceFirstLaunchNumericalCell.actual_launch_seed
    rate source rewards C_star C_h hcross
  rcases hseed with ⟨_, hmode, _, hfirst, _, _, _, _⟩
  have hmode' : ReferenceActivePhysicalHorizon.allActiveAtStart I s := by
    simpa [I, s, ReferenceFirstCollectionEpochAlignment.actualLaunchState,
      ReferenceFirstLaunchNumericalCell.launchState] using hmode
  have hfirst' : I.coordinator = .first := by
    simpa [I, ReferenceFirstCollectionEpochAlignment.actualLaunchState,
      ReferenceFirstLaunchNumericalCell.launchState] using hfirst
  have hCkeep := ReferenceFirstCollectionCompletedPrefix.actual_first_collection_completed_prefix
    rate source rewards C_star C_h count hcross hspan hshort
  have hC := hCkeep
  rcases hC with ⟨cutC, suffixC, seg, hsplitC, hentryC, hsegmentC, hwindowC,
    hsegPrefix, hsegTake, hpartitionB, hsegLength, hsegLookup, hsegCompleted,
    hinputLength, hinputMap, hremaining, hcutFailure, hboundary⟩
  have hshortRun :
      (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (ReferenceActivePhysicalHorizon.run I source.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s count hspan hmode').records).length < count := by
    simpa [I, Erun, s, ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun,
      ReferenceFirstCollectionEpochAlignment.actualLaunchState,
      ReferenceFirstLaunchNumericalCell.launchState] using hshort
  have hO := ReferenceFirstCutoffOutsideInitialization.run_first_cutoff_outside_initializer
    I source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
    s count hspan hmode' hfirst' hshortRun
  rcases hO with ⟨cutO, suffixO, hsplitO, _hindexO, htimeO, _hactualO,
    registers, owned, base, hcutState, hlive, dispatched, hstart, ledger, hinit,
    hledger, hdomain, hclock, hpending, hnoAssignment, cutoffSelection, hcutBranch, hrest⟩
  rcases hrest with ⟨hkpos, hP0sigma, hbase, hfirstBirth, hproposal, hqueues,
    hcutGeometry⟩
  rcases hfirstBirth with ⟨birth, hbirthPrefix, hbirthInstall, hbirthTime,
    installedBirth⟩
  rcases installedBirth with ⟨installed, birthSelection, hbirthChosen,
    hinstalledPayload⟩
  rcases hcutGeometry with ⟨huO, hsigmaPos, huT, huGrid, hgridT,
    hledgerSigma, hledgerCutoff, hfreeze, hfirstCutoff, houtsideSlow,
    houtsideFast, hledgerFields⟩
  let P0 := registers.payload
  have hpreparedCut : (ReferenceActivePhysicalStep.prepare cutO.input).coordinator =
      .live registers owned base (.cutoffChosen dispatched hstart ledger hinit hledger hdomain
        hclock hpending hnoAssignment cutoffSelection) := by
    have h := hcutBranch
    rw [cutO.output_eq] at h
    simpa [ReferenceActivePhysicalStep.step] using h
  have hcutoffTag : ReferenceCollectionPhaseHistory.cutoffChosen cutO.input = true := by
    simp [ReferenceCollectionPhaseHistory.cutoffChosen, hpreparedCut]
  have hsplitO' : Erun.records = W ++ cutO :: suffixO := by
    simpa [Erun, W, I, s, ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun,
      ReferenceFirstCollectionEpochAlignment.actualLaunchState,
      ReferenceFirstLaunchNumericalCell.launchState] using hsplitO
  have htimeO' : cutO.input.time.val = s + w := by
    simpa [Erun, W, w, I, s, ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun,
      ReferenceFirstCollectionEpochAlignment.actualLaunchState,
      ReferenceFirstLaunchNumericalCell.launchState] using htimeO
  have hcutCsplit : Erun.records = W ++ cutC :: suffixC := by
    simpa [Erun, W, ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun,
      ReferenceFirstCollectionEpochAlignment.actualLaunchState,
      ReferenceFirstLaunchNumericalCell.launchState] using hsplitC
  have hcutCeqO : cutC = cutO := by
    have hgetC : Erun.records[w]? = some cutC := by
      rw [hcutCsplit]
      simp [w]
    have hgetO : Erun.records[w]? = some cutO := by
      rw [hsplitO']
      simp [w]
    exact Option.some.inj (hgetC.symm.trans hgetO)
  have hwcount : w < count := by
    simpa [w, W, Erun, ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun,
      ReferenceFirstCollectionEpochAlignment.actualLaunchState,
      ReferenceFirstLaunchNumericalCell.launchState] using hshort
  have hindex : w < Erun.records.length := by
    have hlength : Erun.records.length = count := by
      simpa [Erun, I, s, ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun,
        ReferenceFirstCollectionEpochAlignment.actualLaunchState,
        ReferenceFirstLaunchNumericalCell.launchState] using
        (ReferenceActivePhysicalHorizon.run_record_count I source.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s count hspan hmode')
    omega
  have hcutOIndex : cutO = Erun.records[w]'hindex := by
    have hget : Erun.records[w]? = some cutO := by
      rw [hsplitO']
      simp [w]
    rw [List.getElem?_eq_getElem hindex] at hget
    exact (Option.some.inj hget).symm
  have hcutUnique : ∀ (cut : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
      (suffix : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))),
      Erun.records = W ++ cut :: suffix → cut = cutO := by
    intro cut suffix hsplit
    have hget : Erun.records[w]? = some cut := by rw [hsplit]; simp [w]
    have hgetO : Erun.records[w]? = some cutO := by rw [hsplitO']; simp [w]
    exact Option.some.inj (hget.symm.trans hgetO)
  have htimeWindow := ReferenceFirstCollectionEpochAlignment.actual_first_collection_window_time
    rate source rewards C_star C_h count hcross hspan hshort
  have hrawWindowLookup : ∀ k : Fin B.length,
      Erun.records[w + k.val]? = some B[k.val] ∧
        B[k.val].input.time.val + 1 = u + k.val := by
    intro k
    have hlookup := htimeWindow k
    simpa [Erun, W, w, B, s, u,
      ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun,
      ReferenceFirstCollectionEpochAlignment.actualLaunchState,
      ReferenceFirstLaunchNumericalCell.launchState] using hlookup
  have hBshape : B = cutC :: suffixC.takeWhile
      (fun record => !ReferenceCollectionPhaseHistory.laterChosen record.input) := by
    simpa [B, Erun, W, w, ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun,
      ReferenceFirstCollectionEpochAlignment.actualLaunchState,
      ReferenceFirstLaunchNumericalCell.launchState] using hwindowC
  have hbirthMem : birth ∈ Erun.records := by
    have hprefixMem := run_records_prefix_mem I source.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s w (count - w)
      (by omega) hmode' hbirthPrefix
    simpa [Erun, I, s, ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun,
      ReferenceFirstCollectionEpochAlignment.actualLaunchState,
      ReferenceFirstLaunchNumericalCell.launchState, Nat.add_sub_of_le (Nat.le_of_lt hwcount)]
      using hprefixMem
  have hbirthAtLaunch : birth.input.time.val = s := by
    simpa [s, I, ReferenceFirstCollectionEpochAlignment.actualLaunchState,
      ReferenceFirstLaunchNumericalCell.launchState] using hbirthTime
  have hP0sigma' : P0.sigma.val = s := by simpa [P0, s] using hP0sigma
  have hP0birth : ReferenceAssignmentPayloadPersistence.InstallationBirth birth P0 := by
    simpa [P0] using hbirthInstall
  have hwpos : 0 < w := by
    simpa [w, W, Erun, I, s, ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun,
      ReferenceFirstCollectionEpochAlignment.actualLaunchState,
      ReferenceFirstLaunchNumericalCell.launchState] using hkpos
  have hgetW0 : Erun.records[0]? = some W[0] := by
    rw [hsplitO']
    rw [List.getElem?_append_left (by simpa [w] using hwpos)]
    exact List.getElem?_eq_getElem (by omega : 0 < W.length)
  have htimeW0 := run_record_time_of_lookup I source.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s count hspan hmode'
    0 W[0] hgetW0
  have hW0mem : W[0] ∈ Erun.records := by
    rw [hsplitO']
    exact List.mem_append_left _ (List.getElem_mem (by omega : 0 < W.length))
  have hbirthEqW0 : birth = W[0] :=
    ReferenceAssignmentPayloadChronology.run_records_time_injective I source.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s count hspan hmode'
      hbirthMem hW0mem (by omega)
  obtain ⟨launchSelectionW0, hlaunchSelectionW0, hlaunchPayloadW0⟩ :=
    selection_of_equal_installation_birth birth W[0] P0 hbirthEqW0 hP0birth
  have hfirstPayloadFacts := ReferenceFirstDownRecoveryBudget.run_first_selected_payload
    I source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
    s count hspan hmode' hfirst'
  obtain ⟨birth0, _hbirth0, _hbirthTime0, _hbirth0Install, _hsigma0, hzero0⟩ :=
    hfirstPayloadFacts ⟨0, by omega⟩ launchSelectionW0 hlaunchSelectionW0
  have hP0queues : ∀ a, P0.queues a = 0 := by
    intro a
    simpa only [← hlaunchPayloadW0] using hzero0 a
  have hfirstCutoffO : FollowerCutoffScan.firstCutoff p rate.eta.val P0.sigma
      (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
        (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source))) =
          cutO.input.time.val + 1 := by
    simpa [P0, ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun,
      ReferenceFirstCollectionEpochAlignment.actualLaunchState,
      ReferenceFirstLaunchNumericalCell.launchState] using hfirstCutoff
  have hfirstCutoff' : FollowerCutoffScan.firstCutoff p rate.eta.val P0.sigma
      (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
        (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source))) = u := by
    calc
      _ = cutO.input.time.val + 1 := hfirstCutoffO
      _ = u := by omega
  have hwindowNoLater : ∀ record ∈ B,
      ReferenceCollectionPhaseHistory.laterChosen record.input = false := by
    intro record hmem
    exact laterChosen_false_of_collectionWindow_mem Erun.records w cutC suffixC
      hBshape (by simpa [hcutCeqO] using hcutoffTag) record hmem
  have hselectedPayload :
      ∀ (k : Fin B.length) (n : ℕ)
        (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)),
        n ≤ w + k.val → Erun.records[n]? = some record →
        ∀ (selected : ReferenceActivePhysicalStep.Selection record.input),
          record.output.preparation.coordinator.selection = some selected →
            selected.view.payload = P0 := by
    intro k n record hn hget selected hselection
    have htimeRecord := run_record_time_of_lookup I source.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s count hspan hmode'
      n record (by simpa [Erun, I, s, ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun,
        ReferenceFirstCollectionEpochAlignment.actualLaunchState,
        ReferenceFirstLaunchNumericalCell.launchState] using hget)
    have hrecordMem : record ∈ Erun.records :=
      List.mem_iff_getElem?.mpr ⟨n, hget⟩
    obtain ⟨birthRecord, hbirthRecordMem, hbirthRecord, hbirthLe, hsigmaLe⟩ :=
      ReferenceSelectedPayloadChronology.actualRun_selectedPayload_has_birth
        I source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
        s count hspan hmode' hfirst' record selected hrecordMem hselection
    obtain ⟨b, hbcount, hbirthIndex, hbirthTime⟩ :=
      run_record_mem_index_time I source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
        s count hspan hmode' birthRecord hbirthRecordMem
    have hbirthSigma := ReferenceAssignmentPayloadChronology.installationBirth_time_eq
      birthRecord selected.view.payload hbirthRecord
    obtain ⟨originSelection, horiginSelected, horiginPayload⟩ :=
      selection_of_installation_birth birthRecord selected.view.payload hbirthRecord
    have hbLE : b ≤ n := by omega
    have hbWindow : b < w := by
      by_contra hnot
      have hafter : w ≤ b := Nat.le_of_not_gt hnot
      let q := b - w
      have hqbound : q < B.length := by
        have hbk : b ≤ w + k.val := le_trans hbLE hn
        have hqle : q ≤ k.val := by
          change b - w ≤ k.val
          have hbk' : b ≤ k.val + w := by simpa [Nat.add_comm] using hbk
          exact Nat.sub_le_iff_le_add.mpr hbk'
        exact lt_of_le_of_lt hqle k.isLt
      have hbirthAtB : Erun.records[w + q]? = some B[q] := by
        have hlookup := htimeWindow ⟨q, hqbound⟩
        change Erun.records[w + q]? = some B[q]
        exact hlookup.1
      have hbirthAtIndex : Erun.records[w + q]? = some birthRecord := by
        have hbEq : b = w + q := by
          dsimp [q]
          exact (Nat.add_sub_of_le hafter).symm
        change (ReferenceActivePhysicalHorizon.run I source.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
          s count hspan hmode').records[w + q]? = some birthRecord
        simpa only [hbEq] using hbirthIndex
      have hbirthEqB : birthRecord = B[q] :=
        Option.some.inj (hbirthAtIndex.symm.trans hbirthAtB)
      have hlater := hwindowNoLater (B[q]) (List.getElem_mem hqbound)
      have hpos : 0 < b := lt_of_lt_of_le hwpos hafter
      cases hcoord : birthRecord.output.preparation.coordinator with
      | first outcome =>
          cases outcome with
          | chosen installed choice =>
              have hprepared : (ReferenceActivePhysicalStep.prepare birthRecord.input).coordinator =
                  .first (.chosen installed choice) := by
                have h := hcoord
                rw [birthRecord.output_eq] at h
                simpa [ReferenceActivePhysicalStep.step] using h
              have hstate := input_coordinator_first_of_prepared_first birthRecord.input
                (.chosen installed choice) hprepared
              have hnotfirst := run_record_input_ne_first_of_positive_offset
                I source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
                rewards s count hspan hmode' birthRecord hbirthRecordMem b hpos hbirthTime
              exact (hnotfirst hstate).elim
          | _ => simp [ReferenceAssignmentPayloadPersistence.InstallationBirth,
              hcoord] at hbirthRecord
      | collection payload' ledger clock cutoff outcome =>
          cases outcome with
          | laterChosen core consistent started hstart instruction hinstruction
              output outputConsistent clockData installed choice =>
              have hprepared : (ReferenceActivePhysicalStep.prepare birthRecord.input).coordinator =
                  .collection payload' ledger clock cutoff
                    (.laterChosen core consistent started hstart instruction hinstruction
                      output outputConsistent clockData installed choice) := by
                have h := hcoord
                rw [birthRecord.output_eq] at h
                simpa [ReferenceActivePhysicalStep.step] using h
              have hLater : ReferenceCollectionPhaseHistory.laterChosen birthRecord.input = true := by
                simp [ReferenceCollectionPhaseHistory.laterChosen, hprepared]
              rw [hbirthEqB] at hLater
              rw [hlater] at hLater
              contradiction
          | _ => simp [ReferenceAssignmentPayloadPersistence.InstallationBirth,
              hcoord] at hbirthRecord
      | _ => simp [ReferenceAssignmentPayloadPersistence.InstallationBirth, hcoord] at hbirthRecord
    have hbirthEqW : birthRecord = W[b] := by
      have hgetW : Erun.records[b]? = some W[b] := by
        rw [hcutCsplit]
        rw [List.getElem?_append_left (by simpa [w] using hbWindow)]
        exact List.getElem?_eq_getElem (by omega : b < W.length)
      have hgetBirth : Erun.records[b]? = some birthRecord := by
        change (ReferenceActivePhysicalHorizon.run I source.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
          s count hspan hmode').records[b]? = some birthRecord
        exact hbirthIndex
      exact Option.some.inj (hgetBirth.symm.trans hgetW)
    obtain ⟨originSelectionW, horiginAtW, horiginPayloadW⟩ :=
      selection_transport_of_equal_record birthRecord W[b] originSelection
        hbirthEqW horiginSelected
    have hfirstOrigin := hfirstPayloadFacts ⟨b, hbWindow⟩
      originSelectionW horiginAtW
    rcases hfirstOrigin with ⟨_birthOrigin, _birthOriginMem, _birthOriginTime,
      _birthOriginInstall, hsigmaOrigin, _zeroOrigin⟩
    have hsigmaQuery : selected.view.payload.sigma.val = s := by
      have hpayloadEq : originSelectionW.view.payload = selected.view.payload :=
        horiginPayloadW.trans horiginPayload
      have hsigmaEq := congrArg
        (fun payload : ReferenceActivePhysicalStep.Payload rate => payload.sigma.val) hpayloadEq
      exact hsigmaEq.symm.trans hsigmaOrigin
    have hsamePayload := ReferenceAssignmentPayloadChronology.run_birth_payload_eq_of_equal_sigma
      I source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
      s count hspan hmode' birthRecord birth selected.view.payload P0
      hbirthRecordMem hbirthMem hbirthRecord hP0birth
      (by calc
        selected.view.payload.sigma.val = s := hsigmaQuery
        _ = P0.sigma.val := hP0sigma'.symm)
    exact hsamePayload
  have hretainedPayload :
      ∀ (k : Fin B.length) (n : ℕ)
        (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)),
        n ≤ w + k.val → Erun.records[n]? = some record →
        ∀ (i : Fin (p.m - 1))
          (M : ReferenceAcceptedUpFollowerHistory.DownRecord (p := p) (rate := rate)),
          ReferenceAcceptedUpFollowerHistory.RetainedDown record i M →
            M = P0.downRecord i ∧ M.val.sigma = s + 1 ∧ M.val.q = 0 := by
    intro k n record hn hget i M hretained
    rcases hretained with ⟨logged, cut, after, raw, scan, registers, lastService,
      hinput, hdown, haccepted⟩
    obtain ⟨choice, memory, actualLogged, hconfiguration, hunoccupied, hlogging,
      hactualInput, hcut⟩ :=
      ReferenceFollowerSparseEmissionRecovery.actualDownDiagnostic_choice record i cut hdown
    have hactualIndex := (record.output.preparation.follower_alignment i).2.1
    have hloggedEq : actualLogged = logged := Option.some.inj (hactualInput.symm.trans hinput)
    subst actualLogged
    rw [hcut] at haccepted
    obtain ⟨view, hview⟩ := ReferenceFollowerSparseEmissionRecovery.acceptedReferenceCut_someView
      record.output.preparation.coordinator.downView
      (record.output.preparation.followers.followers i).follower
      (record.output.preparation.followers.followers i).row
      (record.output.preparation.followers.followers i).time
      (record.output.preparation.feedback.observations
        (PublicDiscreteDraws.followerPlayer p.two_le_m i)) logged logged after raw M scan registers
      lastService haccepted
    rw [hview] at haccepted
    have hfields := ReferenceActiveDataOwnership.referenceDown_accepted_fields view
      (record.output.preparation.followers.followers i).follower
      (record.output.preparation.followers.followers i).row
      (record.output.preparation.followers.followers i).time
        (record.output.preparation.feedback.observations
        (PublicDiscreteDraws.followerPlayer p.two_le_m i)) logged logged after raw M scan registers
      lastService haccepted
    have hmap : record.output.preparation.coordinator.selection.map
        ReferenceActivePhysicalStep.Selection.view = some view := by
      change record.output.preparation.coordinator.downView = some view
      exact hview
    obtain ⟨selected, hselection, hselectedView⟩ := Option.map_eq_some_iff.mp hmap
    have hpayload := hselectedPayload k n record hn hget selected hselection
    have hmessage : M = P0.downRecord i := by
      calc
        M = view.payload.downRecord i := by simpa only [hactualIndex] using hfields.1
        _ = selected.view.payload.downRecord i := by simp only [hselectedView]
        _ = P0.downRecord i := congrArg (fun payload : ReferenceActivePhysicalStep.Payload rate =>
          payload.downRecord i) hpayload
    have hsigmaM : M.val.sigma = s + 1 := by
      rw [hmessage]
      simpa [hP0sigma'] using
        (show (P0.downRecord i).val.sigma = P0.sigma.val + 1 by rfl)
    have hqM : M.val.q = 0 := by
      rw [hmessage, P0.downRecord_initialQueue i]
      exact hP0queues _
    exact ⟨hmessage, hsigmaM, hqM⟩
  have hstateCut : cutO.input.state.coordinator = .live registers owned base := by
    rw [hcutState]
    exact hlive
  refine ⟨hCkeep, ?_⟩
  refine ⟨cutO, P0, birth, registers, owned, base,
    ⟨hindex, hcutOIndex⟩, hcutUnique, hstateCut, hcutoffTag, rfl,
    hP0sigma', hP0queues, hfirstCutoff', hbirthMem, hP0birth,
    hbirthAtLaunch, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨installed, birthSelection, hbirthChosen, hinstalledPayload⟩
  · exact hrawWindowLookup
  · intro k record hlookup selected hselection
    exact hselectedPayload k (w + k.val) record (Nat.le_refl _)
      hlookup selected hselection
  · intro k record hlookup i M hretained
    exact hretainedPayload k (w + k.val) record (Nat.le_refl _)
      hlookup i M hretained
  · intro k j hj record hget i M hretained
    exact hretainedPayload k j record (Nat.le_of_lt hj) hget i M hretained
