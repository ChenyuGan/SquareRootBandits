/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceLaterStartUnoccupiedChoice

/-!
# Occupied assignment fields on the actual physical run

Sources: `sources/zip4/manuscript/05_binary_transport.tex:60-88,94-124`,
`sources/zip4/manuscript/06_interruptions.tex:40-69,246-295,327-348`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:54-64`.

The history follows the existing finite physical horizon and its literal
dispatcher selections. It carries the complete selected DOWN payload through
live play, cutoff and collection, and installs the real later-start producer
at each replacement. Failed coordinator tails may discard the stored payload;
an installation birth alone is never used as stored-state evidence.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferenceAssignmentPayloadChronology
open Bandits.Support.ReferenceAssignmentPayloadPersistence
open Bandits.Support.ReferenceActiveDataOwnership

namespace Bandits.Support.ReferenceOccupiedFieldHistory

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput

variable {p : Parameters} {rate : RateInput p}

private theorem selectionAt_payload_eq
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (payload : Payload rate)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (time : Fin p.T)
    (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ)
    (choice : CoordinatorRoundDispatch.ArmSelection payload started time weights x.row)
    (selected : ReferenceActivePhysicalStep.Selection x)
    (hselection : ReferenceActivePhysicalStep.selectionAt x payload started time weights choice =
      some selected) :
    selected.view.payload = payload := by
  by_cases htime : time = x.time
  · simp only [ReferenceActivePhysicalStep.selectionAt, dite_eq_left htime] at hselection
    exact congrArg (fun value : ReferenceActivePhysicalStep.Selection x => value.view.payload)
      (Option.some.inj hselection).symm
  · simp only [ReferenceActivePhysicalStep.selectionAt, dite_eq_right htime] at hselection
    cases hselection

private theorem input_coordinator_first_of_prepared_first
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

private theorem selected_payload_eq_of_installation_birth
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (selected : ReferenceActivePhysicalStep.Selection x)
    (hselected : (ReferenceActivePhysicalStep.prepare x).coordinator.selection = some selected)
    (fresh : Payload rate)
    (hbirth : ReferenceAssignmentPayloadPersistence.InstallationBirth
      (ReferenceAssignmentPayloadChronology.actualStepRecord x) fresh) :
    selected.view.payload = fresh := by
  cases hcoord : (ReferenceActivePhysicalStep.prepare x).coordinator with
  | first outcome =>
      cases outcome with
      | chosen installed choice =>
          have hselectionAt : ReferenceActivePhysicalStep.selectionAt x installed.registers.payload
              installed.startRoundResult installed.registers.time installed.registers.complementWeights
              choice = some selected := by
            simpa [hcoord, ReferenceActivePhysicalStep.DispatchCut.selection] using hselected
          have hview := selectionAt_payload_eq x installed.registers.payload
            installed.startRoundResult installed.registers.time installed.registers.complementWeights
            choice selected hselectionAt
          have hb : fresh = installed.registers.payload := by
            have hb' : fresh = installed.registers.payload ∧
                (fresh.sigma : ℕ) = (x.time : ℕ) := by
              simpa [ReferenceAssignmentPayloadPersistence.InstallationBirth,
                ReferenceAssignmentPayloadChronology.actualStepRecord,
                ReferenceActivePhysicalStep.step, hcoord] using hbirth
            exact hb'.1
          exact hview.trans hb.symm
      | _ => simp [ReferenceActivePhysicalStep.DispatchCut.selection, hcoord] at hselected
  | live registers owned base outcome =>
      simp [ReferenceAssignmentPayloadPersistence.InstallationBirth,
        ReferenceAssignmentPayloadChronology.actualStepRecord,
        ReferenceActivePhysicalStep.step, hcoord] at hbirth
  | collection payload ledger clock cutoff outcome =>
      cases outcome with
      | laterChosen core consistent started startRound_eq instruction assignmentStart_eq
          output consistency clockData installed choice =>
          have hselectionAt : ReferenceActivePhysicalStep.selectionAt x installed.registers.payload
              started instruction.time installed.registers.complementWeights choice = some selected := by
            simpa [hcoord, ReferenceActivePhysicalStep.DispatchCut.selection] using hselected
          have hview := selectionAt_payload_eq x installed.registers.payload started instruction.time
            installed.registers.complementWeights choice selected hselectionAt
          have hb : fresh = installed.registers.payload := by
            have hb' : fresh = installed.registers.payload ∧
                (fresh.sigma : ℕ) = (x.time : ℕ) := by
              simpa [ReferenceAssignmentPayloadPersistence.InstallationBirth,
                ReferenceAssignmentPayloadChronology.actualStepRecord,
                ReferenceActivePhysicalStep.step, hcoord] using hbirth
            exact hb'.1
          exact hview.trans hb.symm
      | _ => simp [ReferenceAssignmentPayloadPersistence.InstallationBirth,
          ReferenceAssignmentPayloadChronology.actualStepRecord,
          ReferenceActivePhysicalStep.step, hcoord] at hbirth
  | invalidCollectionCutoff =>
      simp [ReferenceAssignmentPayloadPersistence.InstallationBirth,
        ReferenceAssignmentPayloadChronology.actualStepRecord,
        ReferenceActivePhysicalStep.step, hcoord] at hbirth
  | dagger =>
      simp [ReferenceAssignmentPayloadPersistence.InstallationBirth,
        ReferenceAssignmentPayloadChronology.actualStepRecord,
        ReferenceActivePhysicalStep.step, hcoord] at hbirth

private theorem installation_output_stored_frame
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (selected : ReferenceActivePhysicalStep.Selection x)
    (hselected : (ReferenceActivePhysicalStep.prepare x).coordinator.selection = some selected)
    (hbirth : ReferenceAssignmentPayloadPersistence.InstallationBirth
      (ReferenceAssignmentPayloadChronology.actualStepRecord x) selected.view.payload) :
    ReferenceAssignmentPayloadPersistence.storedPayload
        (ReferenceActivePhysicalStep.step x).next.coordinator = none ∨
      ReferenceAssignmentPayloadPersistence.storedPayload
        (ReferenceActivePhysicalStep.step x).next.coordinator = some selected.view.payload := by
  cases hcoord : (ReferenceActivePhysicalStep.prepare x).coordinator with
  | first outcome =>
      cases outcome with
      | chosen installed choice =>
          have hselectionAt : ReferenceActivePhysicalStep.selectionAt x installed.registers.payload
              installed.startRoundResult installed.registers.time installed.registers.complementWeights
              choice = some selected := by
            simpa [hcoord, ReferenceActivePhysicalStep.DispatchCut.selection] using hselected
          have hview := selectionAt_payload_eq x installed.registers.payload
            installed.startRoundResult installed.registers.time installed.registers.complementWeights
            choice selected hselectionAt
          have hcut : (ReferenceActivePhysicalStep.DispatchCut.first (.chosen installed choice)).selection =
              some selected := by
            simpa [hcoord] using hselected
          have hnonempty : (ReferenceActivePhysicalStep.DispatchCut.first (.chosen installed choice)).selection ≠
              none := by
            rw [hcut]
            exact Option.some_ne_none _
          have hobserve := ReferenceActivePhysicalStep.observeCoordinator_first_equation
            (ReferenceActivePhysicalStep.prepare x) (.chosen installed choice) hcoord
          have hobserve' : (ReferenceActivePhysicalStep.prepare x).observeCoordinator.configuration =
              (ReferenceActivePhysicalStep.livePostChoice (ReferenceActivePhysicalStep.prepare x)
                installed.registers installed.ownedRegisters installed.followerBaseScore
                installed.startRoundResult).configuration := by
            rw [hobserve]
            simp only [hnonempty, ite_false]
          have hframe := ReferenceAssignmentPayloadPersistence.livePostChoice_payload_frame
            (ReferenceActivePhysicalStep.prepare x) installed.registers installed.ownedRegisters
            installed.followerBaseScore installed.startRoundResult
          rw [(ReferenceActivePhysicalStep.step_next_fields x).1, hobserve']
          rcases hframe with hnone | hsome
          · exact Or.inl hnone
          · exact Or.inr (by rw [hview]; exact hsome)
      | _ => simp [ReferenceAssignmentPayloadPersistence.InstallationBirth,
          ReferenceAssignmentPayloadChronology.actualStepRecord,
          ReferenceActivePhysicalStep.step, hcoord] at hbirth
  | live registers owned base outcome =>
      simp [ReferenceAssignmentPayloadPersistence.InstallationBirth,
        ReferenceAssignmentPayloadChronology.actualStepRecord,
        ReferenceActivePhysicalStep.step, hcoord] at hbirth
  | collection payload ledger clock cutoff outcome =>
      cases outcome with
      | laterChosen core consistent started startRound_eq instruction assignmentStart_eq
          output consistency clockData installed choice =>
          have hselectionAt : ReferenceActivePhysicalStep.selectionAt x installed.registers.payload
              started instruction.time installed.registers.complementWeights choice = some selected := by
            simpa [hcoord, ReferenceActivePhysicalStep.DispatchCut.selection] using hselected
          have hview := selectionAt_payload_eq x installed.registers.payload started instruction.time
            installed.registers.complementWeights choice selected hselectionAt
          have hcut : (ReferenceActivePhysicalStep.DispatchCut.collection payload ledger clock cutoff
              (.laterChosen core consistent started startRound_eq instruction assignmentStart_eq
                output consistency clockData installed choice)).selection = some selected := by
            simpa [hcoord] using hselected
          have hnonempty := Option.some_ne_none selected
          have hobserve := ReferenceActivePhysicalStep.observeCoordinator_collection_equation
            (ReferenceActivePhysicalStep.prepare x) payload ledger clock cutoff
            (.laterChosen core consistent started startRound_eq instruction assignmentStart_eq
              output consistency clockData installed choice) hcoord
          have hobserve' : (ReferenceActivePhysicalStep.prepare x).observeCoordinator.configuration =
              (ReferenceActivePhysicalStep.livePostChoice (ReferenceActivePhysicalStep.prepare x)
                installed.registers installed.ownedRegisters installed.retainedBaseScore started).configuration := by
            rw [hobserve]
            simp only [hcut, ite_eq_right hnonempty]
          have hframe := ReferenceAssignmentPayloadPersistence.livePostChoice_payload_frame
            (ReferenceActivePhysicalStep.prepare x) installed.registers installed.ownedRegisters
            installed.retainedBaseScore started
          rw [(ReferenceActivePhysicalStep.step_next_fields x).1, hobserve']
          rcases hframe with hnone | hsome
          · exact Or.inl hnone
          · exact Or.inr (by rw [hview]; exact hsome)
      | _ => simp [ReferenceAssignmentPayloadPersistence.InstallationBirth,
          ReferenceAssignmentPayloadChronology.actualStepRecord,
          ReferenceActivePhysicalStep.step, hcoord] at hbirth
  | invalidCollectionCutoff =>
      simp [ReferenceAssignmentPayloadPersistence.InstallationBirth,
        ReferenceAssignmentPayloadChronology.actualStepRecord,
        ReferenceActivePhysicalStep.step, hcoord] at hbirth
  | dagger =>
      simp [ReferenceAssignmentPayloadPersistence.InstallationBirth,
        ReferenceAssignmentPayloadChronology.actualStepRecord,
        ReferenceActivePhysicalStep.step, hcoord] at hbirth

private theorem selected_output_stored_payload_eq
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (selected : ReferenceActivePhysicalStep.Selection x)
    (hselected : (ReferenceActivePhysicalStep.prepare x).coordinator.selection = some selected)
    (payload : Payload rate)
    (hstored : ReferenceAssignmentPayloadPersistence.storedPayload
      (ReferenceActivePhysicalStep.step x).next.coordinator = some payload) :
    payload = selected.view.payload := by
  have hclass := ReferenceAssignmentPayloadChronology.actualStep_payload_classification x
  rcases hclass with hnone | ⟨old, hbefore, hafter⟩ | ⟨fresh, hbirth, hafter⟩
  · rw [hnone] at hstored
    cases hstored
  · have hlocal := ReferenceSelectedPayloadChronology.actualSelectedPayload_local_stored_or_birth
      (ReferenceAssignmentPayloadChronology.actualStepRecord x) selected (by
        simpa [ReferenceAssignmentPayloadChronology.actualStepRecord,
          ReferenceActivePhysicalStep.step] using hselected)
    rcases hlocal with hselectedStored | hselectedBirth
    · have hselOld : selected.view.payload = old := Option.some.inj (hselectedStored.symm.trans hbefore)
      have hpOld : payload = old := Option.some.inj (hstored.symm.trans hafter)
      exact hpOld.trans hselOld.symm
    · have hframe := installation_output_stored_frame x selected hselected hselectedBirth
      rcases hframe with hnone | hsome
      · rw [hnone] at hstored
        cases hstored
      · exact Option.some.inj (hstored.symm.trans hsome)
  · have hselFresh := selected_payload_eq_of_installation_birth x selected hselected fresh hbirth
    have hpFresh : payload = fresh := Option.some.inj (hstored.symm.trans hafter)
    exact hpFresh.trans hselFresh.symm

private theorem livePostChoice_configuration_ne_first
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
          | error reason => simp [hledger, hclock,
              ReferenceActivePhysicalStep.coordinatorFailure]
          | ok finishedClock => simp [hledger, hclock]
  | rejected pair =>
      rcases pair with ⟨ledger, bank⟩
      cases hledger : CoordinatorCollectionLedger.finishRound ledger with
      | invalid => simp [hledger, ReferenceActivePhysicalStep.coordinatorFailure]
      | rejected rejected => simp [hledger, ReferenceActivePhysicalStep.coordinatorFailure]
      | success finishedLedger =>
          cases hclock : CoordinatorPhaseClock.finishRound p rate.eta.val x.time
              started.clock finishedLedger.pending x.row with
          | error reason => simp [hledger, hclock,
              ReferenceActivePhysicalStep.coordinatorFailure]
          | ok finishedClock => simp [hledger, hclock]

private theorem collectionPostChoice_configuration_ne_first
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

private theorem step_coordinator_ne_first (x : ReferenceActivePhysicalStep.RoundInput p rate) :
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
              (ReferenceActivePhysicalStep.prepare x) (ReferenceActivePhysicalStep.liveRegistersAt registers x.time)
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

private theorem run_prefix_final_coordinator_first_only
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (J : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start totalCount : ℕ) (hspan : start + totalCount ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (prefixLength : ℕ) (hprefix : prefixLength ≤ totalCount)
    (hcoord : (ReferenceActivePhysicalHorizon.run initial rows J rewards start prefixLength
      (by omega) active).finalState.coordinator = .first) :
    prefixLength = 0 := by
  cases prefixLength with
  | zero => rfl
  | succ prefixLength =>
      have hfinal := ReferenceAssignmentPayloadChronology.run_successor_finalState_eq_actualRunRecordAt
        initial rows J rewards start prefixLength (by omega) active
      have hrecord : ReferenceAssignmentPayloadChronology.actualRunRecordAt initial rows J rewards
          start prefixLength (by omega) active =
            ReferenceAssignmentPayloadChronology.actualStepRecord
              (ReferenceCollectionPhaseHistory.nextInput initial rows J rewards start prefixLength
                (by omega) active) := rfl
      rw [hfinal, hrecord] at hcoord
      exact (step_coordinator_ne_first _ hcoord).elim

private theorem selected_birth_origin
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (selected : ReferenceActivePhysicalStep.Selection x)
    (hselected : (ReferenceActivePhysicalStep.prepare x).coordinator.selection = some selected)
    (hbirth : ReferenceAssignmentPayloadPersistence.InstallationBirth
      (ReferenceAssignmentPayloadChronology.actualStepRecord x) selected.view.payload) :
    x.state.coordinator = .first ∨ ReferenceCollectionPhaseHistory.laterChosen x = true := by
  cases hcoord : (ReferenceActivePhysicalStep.prepare x).coordinator with
  | first outcome =>
      cases outcome with
      | chosen installed choice =>
          exact Or.inl (input_coordinator_first_of_prepared_first x
            (.chosen installed choice) hcoord)
      | _ => simp [ReferenceActivePhysicalStep.DispatchCut.selection, hcoord] at hselected
  | live registers owned base outcome =>
      simp [ReferenceAssignmentPayloadPersistence.InstallationBirth,
        ReferenceAssignmentPayloadChronology.actualStepRecord,
        ReferenceActivePhysicalStep.step, hcoord] at hbirth
  | collection payload ledger clock cutoff outcome =>
      cases outcome with
      | laterChosen core consistent started startRound instruction assignmentStart output
          consistency clockData installed choice =>
          exact Or.inr (by simp [ReferenceCollectionPhaseHistory.laterChosen, hcoord])
      | _ => simp [ReferenceAssignmentPayloadPersistence.InstallationBirth,
          ReferenceAssignmentPayloadChronology.actualStepRecord,
          ReferenceActivePhysicalStep.step, hcoord] at hbirth
  | invalidCollectionCutoff =>
      simp [ReferenceAssignmentPayloadPersistence.InstallationBirth,
        ReferenceAssignmentPayloadChronology.actualStepRecord,
        ReferenceActivePhysicalStep.step, hcoord] at hbirth
  | dagger =>
      simp [ReferenceAssignmentPayloadPersistence.InstallationBirth,
        ReferenceAssignmentPayloadChronology.actualStepRecord,
        ReferenceActivePhysicalStep.step, hcoord] at hbirth

private theorem selected_birth_input_fields
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (J : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start totalCount : ℕ) (hspan : start + totalCount ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hfirst : initial.coordinator = .first)
    (hseed : ∀ i s memory, initial.followers i = .ordinary s memory →
      s.status = .unoccupied)
    (index : ℕ) (hindex : index < totalCount)
    (selected : ReferenceActivePhysicalStep.Selection
      (ReferenceCollectionPhaseHistory.nextInput initial rows J rewards start index
        (by omega) active))
    (hselected : (ReferenceActivePhysicalStep.prepare
      (ReferenceCollectionPhaseHistory.nextInput initial rows J rewards start index
        (by omega) active)).coordinator.selection = some selected)
    (hbirth : ReferenceAssignmentPayloadPersistence.InstallationBirth
      (ReferenceAssignmentPayloadChronology.actualStepRecord
        (ReferenceCollectionPhaseHistory.nextInput initial rows J rewards start index
          (by omega) active)) selected.view.payload) :
    ReferenceActiveDataOwnership.carriedOccupiedFields selected.view.payload
      (ReferenceCollectionPhaseHistory.nextInput initial rows J rewards start index
        (by omega) active).state := by
  let x := ReferenceCollectionPhaseHistory.nextInput initial rows J rewards start index
    (by omega) active
  have horigin := selected_birth_origin x selected hselected hbirth
  rcases horigin with hstateFirst | hlater
  · have hprefixFirst : (ReferenceActivePhysicalHorizon.run initial rows J rewards start index
        (by omega) active).finalState.coordinator = .first := by
      change (ReferenceActivePhysicalHorizon.run initial rows J rewards start index
        (by omega) active).finalState.coordinator = .first at hstateFirst
      exact hstateFirst
    have hzero := run_prefix_final_coordinator_first_only initial rows J rewards start totalCount
      hspan active index (by omega) hprefixFirst
    subst index
    have hxstate : x.state = initial := by
      change (ReferenceActivePhysicalHorizon.run initial rows J rewards start 0
        (by omega) active).finalState = initial
      exact (ReferenceActivePhysicalHorizon.run_zero_final initial rows J rewards start
        (by omega) active).symm
    rw [hxstate]
    intro i
    cases hi : initial.followers i with
    | dagger => simp only [ReferenceActiveDataOwnership.occupiedFields]
    | ordinary s memory =>
        simp only [ReferenceActiveDataOwnership.occupiedFields]
        intro hoccupied
        exact (hoccupied (hseed i s memory hi)).elim
  · have hlaterFields := ReferenceLaterStartUnoccupiedChoice.run_laterChosen_step_occupied_fields
      initial rows J rewards start index (by omega) active hfirst hlater selected hselected
    exact hlaterFields.2.1

private theorem prepared_selected_occupied_fields
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (selected : ReferenceActivePhysicalStep.Selection x)
    (hfields : ReferenceActiveDataOwnership.carriedOccupiedFields selected.view.payload x.state) :
    ∀ i, ReferenceActiveDataOwnership.occupiedFields selected.view.payload i
      ((ReferenceActivePhysicalStep.prepare x).followers.followers i).configuration := by
  intro i
  rw [(ReferenceActivePhysicalStep.prepare x).followers.followers_eq i]
  exact ReferenceActiveDataOwnership.choice_occupied_fields_preserved selected.view.payload i
    x.row (x.state.activations i) x.time (x.active i) (x.state.followers i) (hfields i)

/-- The actual finite run's complete assignment-field history. Every stored
payload at every boundary has its carried fields; every actual selected view
has the same payload on its incoming state, its prepared follower choices, and
the step output. The source-launch seed is conditional and explicit. -/
theorem run_prefix_occupied_field_history
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (J : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start totalCount : ℕ) (hspan : start + totalCount ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hfirst : initial.coordinator = .first)
    (hseed : ∀ i s memory, initial.followers i = .ordinary s memory →
      s.status = .unoccupied)
    (prefixLength : ℕ) (hprefix : prefixLength ≤ totalCount) :
    (∀ payload : ReferenceActivePhysicalStep.Payload rate,
      ReferenceAssignmentPayloadPersistence.storedPayload
        (ReferenceActivePhysicalHorizon.run initial rows J rewards start prefixLength
          (by omega) active).finalState.coordinator = some payload →
      ReferenceActiveDataOwnership.carriedOccupiedFields payload
        (ReferenceActivePhysicalHorizon.run initial rows J rewards start prefixLength
          (by omega) active).finalState) ∧
    (∀ record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate),
      record ∈ (ReferenceActivePhysicalHorizon.run initial rows J rewards start prefixLength
        (by omega) active).records →
      ∀ selected : ReferenceActivePhysicalStep.Selection record.input,
        record.output.preparation.coordinator.selection = some selected →
        ReferenceActiveDataOwnership.carriedOccupiedFields selected.view.payload record.input.state ∧
        (∀ i, ReferenceActiveDataOwnership.occupiedFields selected.view.payload i
          (record.output.preparation.followers.followers i).configuration) ∧
        ReferenceActiveDataOwnership.carriedOccupiedFields selected.view.payload record.output.next) := by
  induction prefixLength with
  | zero =>
      constructor
      · intro payload hstored
        rw [ReferenceActivePhysicalHorizon.run_zero_final initial rows J rewards start
          (by omega) active] at hstored
        simp [hfirst, ReferenceAssignmentPayloadPersistence.storedPayload] at hstored
      · intro record hrecord
        rw [ReferenceActivePhysicalHorizon.run_zero_records initial rows J rewards start
          (by omega) active] at hrecord
        cases hrecord
  | succ index ih =>
      have hindex : index < totalCount := by omega
      have hprefixPrev : index ≤ totalCount := by omega
      let x := ReferenceCollectionPhaseHistory.nextInput initial rows J rewards start index
        (by omega) active
      let record := ReferenceAssignmentPayloadChronology.actualStepRecord x
      have hrecordEq : ReferenceAssignmentPayloadChronology.actualRunRecordAt initial rows J rewards
          start index (by omega) active = record := rfl
      have hsuccRecords :
          (ReferenceActivePhysicalHorizon.run initial rows J rewards start (index + 1)
            (by omega) active).records =
            (ReferenceActivePhysicalHorizon.run initial rows J rewards start index
              (by omega) active).records ++ [record] := by
        rw [ReferenceAssignmentPayloadChronology.run_successor_actualRunRecordAt
          initial rows J rewards start index (by omega) active]
        rfl
      have hfinal :
          (ReferenceActivePhysicalHorizon.run initial rows J rewards start (index + 1)
            (by omega) active).finalState = record.output.next := by
        rw [ReferenceAssignmentPayloadChronology.run_successor_finalState_eq_actualRunRecordAt
          initial rows J rewards start index (by omega) active, hrecordEq]
      have hnewRecordHistory :
          ∀ selected : ReferenceActivePhysicalStep.Selection record.input,
            record.output.preparation.coordinator.selection = some selected →
            ReferenceActiveDataOwnership.carriedOccupiedFields selected.view.payload record.input.state ∧
            (∀ i, ReferenceActiveDataOwnership.occupiedFields selected.view.payload i
              (record.output.preparation.followers.followers i).configuration) ∧
            ReferenceActiveDataOwnership.carriedOccupiedFields selected.view.payload record.output.next := by
        intro selected hselected
        have hselectedInput : (ReferenceActivePhysicalStep.prepare x).coordinator.selection = some selected := by
          simpa [record, ReferenceAssignmentPayloadChronology.actualStepRecord,
            ReferenceActivePhysicalStep.step] using hselected
        have hlocal := ReferenceSelectedPayloadChronology.actualSelectedPayload_local_stored_or_birth
          record selected hselected
        have hinputFields : ReferenceActiveDataOwnership.carriedOccupiedFields
            selected.view.payload x.state := by
          rcases hlocal with hstored | hbirth
          · have hstoredPrev : ReferenceAssignmentPayloadPersistence.storedPayload
                (ReferenceActivePhysicalHorizon.run initial rows J rewards start index
                  (by omega) active).finalState.coordinator = some selected.view.payload := by
              simpa [x, ReferenceCollectionPhaseHistory.nextInput,
                ReferenceActivePhysicalHorizon.roundInputAt, record,
                ReferenceAssignmentPayloadChronology.actualStepRecord] using hstored
            simpa [x, ReferenceCollectionPhaseHistory.nextInput,
              ReferenceActivePhysicalHorizon.roundInputAt, record,
              ReferenceAssignmentPayloadChronology.actualStepRecord] using
              (ih hprefixPrev).1 selected.view.payload hstoredPrev
          · exact selected_birth_input_fields initial rows J rewards start totalCount hspan
              active hfirst hseed index hindex selected hselectedInput hbirth
        have hprepared := prepared_selected_occupied_fields x selected hinputFields
        have houtput := ReferenceActiveDataOwnership.step_occupied_fields x selected hselectedInput
          hinputFields
        exact ⟨by simpa [record, ReferenceAssignmentPayloadChronology.actualStepRecord,
            ReferenceActivePhysicalStep.step] using hinputFields,
          by simpa [record, ReferenceAssignmentPayloadChronology.actualStepRecord,
            ReferenceActivePhysicalStep.step] using hprepared,
          by simpa [record, ReferenceAssignmentPayloadChronology.actualStepRecord,
            ReferenceActivePhysicalStep.step] using houtput⟩
      constructor
      · intro payload hstored
        have hstoredRecord : ReferenceAssignmentPayloadPersistence.storedPayload
            record.output.next.coordinator = some payload := by
          rw [← hfinal]
          exact hstored
        have hstoredStep : ReferenceAssignmentPayloadPersistence.storedPayload
            (ReferenceActivePhysicalStep.step x).next.coordinator = some payload := by
          simpa [record, ReferenceAssignmentPayloadChronology.actualStepRecord,
            ReferenceActivePhysicalStep.step] using hstoredRecord
        cases hselection : (ReferenceActivePhysicalStep.prepare x).coordinator.selection with
        | none =>
            have hnone : ReferenceAssignmentPayloadPersistence.storedPayload
                record.output.next.coordinator = none :=
              ReferenceAssignmentPayloadChronology.actualRecord_next_storedPayload_none_of_no_selection
                record (by simpa [record, ReferenceAssignmentPayloadChronology.actualStepRecord,
                  ReferenceActivePhysicalStep.step] using hselection)
            rw [hnone] at hstoredRecord
            cases hstoredRecord
        | some selected =>
            have hselected : (ReferenceActivePhysicalStep.prepare x).coordinator.selection = some selected := hselection
            have hselectedRecord : record.output.preparation.coordinator.selection = some selected := by
              simpa [record, ReferenceAssignmentPayloadChronology.actualStepRecord,
                ReferenceActivePhysicalStep.step] using hselected
            have hhistory := hnewRecordHistory selected (by
              exact hselectedRecord)
            have hpayload := selected_output_stored_payload_eq x selected hselected payload hstoredStep
            have hfields : ReferenceActiveDataOwnership.carriedOccupiedFields payload
                (ReferenceActivePhysicalHorizon.run initial rows J rewards start (index + 1)
                  (by omega) active).finalState := by
              rw [hfinal]
              have hout : ReferenceActiveDataOwnership.carriedOccupiedFields
                  selected.view.payload record.output.next := by
                exact hhistory.2.2
              rw [hpayload]
              exact hout
            exact hfields
      · intro old hmem selected hselected
        rw [hsuccRecords] at hmem
        rcases List.mem_append.mp hmem with hprior | hlast
        · exact (ih hprefixPrev).2 old hprior selected hselected
        · have heq : old = record := List.mem_singleton.mp hlast
          subst old
          exact hnewRecordHistory selected hselected

private theorem carried_to_prepared_state_agreement
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (selected : ReferenceActivePhysicalStep.Selection x)
    (states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
    (memories : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p)
    (hordinary : ∀ i, ((ReferenceActivePhysicalStep.prepare x).followers.followers i).configuration =
      .ordinary (states i) (memories i))
    (hprepared : ∀ i, ReferenceActiveDataOwnership.occupiedFields selected.view.payload i
      ((ReferenceActivePhysicalStep.prepare x).followers.followers i).configuration) :
    ∀ i, (states i).status ≠ .unoccupied →
      (states i).lastDown = some (selected.view.payload.downRecord i) := by
  intro i hoccupied
  have h := hprepared i
  rw [hordinary i] at h
  exact h hoccupied

/-- The actual physical DATA consumer. All ordinary choice configurations and
the real DATA/live/ownership/recording-mask selectors stay explicit. The
occupied last-DOWN field input is produced from the run history and is not a
caller-supplied premise. -/
theorem run_record_owner_feedback
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (J : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hfirst : initial.coordinator = .first)
    (hseed : ∀ i s memory, initial.followers i = .ordinary s memory →
      s.status = .unoccupied)
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hrecord : record ∈ (ReferenceActivePhysicalHorizon.run initial rows J rewards
      start count hspan active).records)
    (selected : ReferenceActivePhysicalStep.Selection record.input)
    (hselected : record.output.preparation.coordinator.selection = some selected)
    (states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
    (memories : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p)
    (hordinary : ∀ i, ((ReferenceActivePhysicalStep.prepare record.input).followers.followers i).configuration =
      .ordinary (states i) (memories i))
    (hlive : CoordinatorLocalArmChoice.assignmentIsLive selected.view.payload selected.view.cutoff
      record.input.time)
    (hdata : Bandits.Support.PublicDiscreteDraws.slotDraw
      (record.input.row.2 record.input.time).1 = Bandits.Support.PublicDiscreteDraws.dataSlot)
    (owner : Fin p.m) (j : Fin p.K)
    (haction : (ReferenceActivePhysicalStep.prepare record.input).arms.actions owner = j)
    (howns : SnapshotRecordingKernel.owns p
      (.live selected.view.payload.assignment (ReferenceActiveDataOwnership.choiceSnapshot selected states))
      owner j)
    (hmask : CanonicalRecordingSlice.recordingMask (K_pos p) owner j
      (record.input.row.2 record.input.time).1) :
    record.gridFeedback owner = rewards record.input.time j ∧
      ReferenceActivePhysicalHorizon.observationValue (record.ownEntries owner).2 =
        ((rewards record.input.time j).val : ℝ) / (D p : ℝ) := by
  have hhistory := run_prefix_occupied_field_history initial rows J rewards start count hspan
    active hfirst hseed count le_rfl
  have hfieldsPrepared := (hhistory.2 record hrecord selected hselected).2.1
  have hselectedInput : (ReferenceActivePhysicalStep.prepare record.input).coordinator.selection =
      some selected := by
    simpa [record.output_eq, ReferenceActivePhysicalStep.step] using hselected
  have hfieldsPreparedInput : ∀ i,
      ReferenceActiveDataOwnership.occupiedFields selected.view.payload i
        ((ReferenceActivePhysicalStep.prepare record.input).followers.followers i).configuration := by
    intro i
    simpa [record.output_eq, ReferenceActivePhysicalStep.step] using hfieldsPrepared i
  have hfields := carried_to_prepared_state_agreement record.input selected states memories
    hordinary hfieldsPreparedInput
  exact ReferenceActiveDataOwnership.run_record_owner_feedback initial rows J rewards start count
    hspan active record hrecord selected hselectedInput states memories hordinary hfields hlive hdata
    owner j haction howns hmask

/-- Actual launched-boundary specialization, using the original source and
private arrays (including its selected row). The admitted replay producer
supplies the first tag, activation bound, and ordinary unoccupied/no-DOWN
seed; all launch relation, clean-prefix, generated-DOWN, forced, and computed
handoff conditions remain explicit. -/
theorem ofActualLaunchedBoundary_occupied_field_history
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (rate : ReferenceActivePhysicalStep.RateInput p) (C_star C_h : ℝ)
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
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
          b h).uninformed),
      BootstrapAllCandidateController.cleanPrefix
        (ReferenceInitializationRun.physical
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
          b h)
        source.1.2 ⟨ActualReferenceInitializationBlock.refFollower i, hi⟩
        (ActualInitializationPhysicalStep.selectedRowIndex p source) p.T)
    (hforce : ∀ i, ReferenceInitializationRun.forced
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
      b h i = false)
    (launch : BootstrapCoordinatorLocalRound.LaunchedBlock p)
    (learnerSeed : ActualInitializationRun.CoordinatorLearnerZeroSeed p)
    (hlaunched : (ActualInitializationRun.combinedBoundaryHandoff p rate
      (ReferenceInitializationRun.nextBlock b h) source rewards actual.C_star actual.C_h
      (ActualInitializationRun.foldBlock p rate (ReferenceInitializationRun.nextBlock b h)
        source rewards actual)).disposition = .launched launch learnerSeed)
    (count : ℕ)
    (span : BootstrapObservedFollower.blockStop p (ReferenceInitializationRun.nextBlock b h) +
      (count + 1) ≤ p.T) :
    let initial := ActualInitializationLaunchState.ofActualLaunchedBoundary source rewards rate
      C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed hlaunched
    let start := BootstrapObservedFollower.blockStop p (ReferenceInitializationRun.nextBlock b h)
    let active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start :=
      fun player => ActualInitializationLaunchState.ofActualLaunchedBoundary_activation_le_blockStop
        source rewards rate C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed
        hlaunched player
    initial.coordinator = .first ∧
      (∀ i, ∃ state memory, initial.followers i = .ordinary state memory ∧
        state.lastDown = none ∧ state.status = .unoccupied) ∧
      ReferenceActivePhysicalHorizon.allActiveAtStart initial start ∧
      (∀ payload : ReferenceActivePhysicalStep.Payload rate,
          ReferenceAssignmentPayloadPersistence.storedPayload
            (ReferenceActivePhysicalHorizon.run initial source.1.2
              (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start (count + 1)
              span active).finalState.coordinator = some payload →
          ReferenceActiveDataOwnership.carriedOccupiedFields payload
            (ReferenceActivePhysicalHorizon.run initial source.1.2
              (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start (count + 1)
              span active).finalState) ∧
        (∀ record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate),
          record ∈ (ReferenceActivePhysicalHorizon.run initial source.1.2
            (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start (count + 1)
            span active).records →
          ∀ selected : ReferenceActivePhysicalStep.Selection record.input,
            record.output.preparation.coordinator.selection = some selected →
            ReferenceActiveDataOwnership.carriedOccupiedFields selected.view.payload record.input.state ∧
            (∀ i, ReferenceActiveDataOwnership.occupiedFields selected.view.payload i
              (record.output.preparation.followers.followers i).configuration) ∧
            ReferenceActiveDataOwnership.carriedOccupiedFields selected.view.payload record.output.next) := by
  intro initial start active
  have hboundary := ReferenceLaterStartUnoccupiedChoice.ofActualLaunchedBoundary_laterChosen_ordinary_choice_unoccupied
    source rewards rate C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed
    hlaunched count span
  rcases hboundary with ⟨hfirst, hfollowers, _⟩
  have hseed : ∀ i state memory, initial.followers i = .ordinary state memory →
      state.status = .unoccupied := by
    intro i state memory hi
    obtain ⟨first, firstMemory, hconfig, _, _, hunoccupied⟩ := hfollowers i
    have hEq : first = state := by
      exact (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
        (hconfig.symm.trans hi)).1
    simpa [hEq] using hunoccupied
  refine ⟨hfirst, ?_⟩
  constructor
  · intro i
    obtain ⟨first, firstMemory, hconfig, hstate, hlast, hunoccupied⟩ := hfollowers i
    exact ⟨first, firstMemory, hconfig, hlast, hunoccupied⟩
  constructor
  · exact active
  · exact run_prefix_occupied_field_history initial source.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start (count + 1)
      span active hfirst hseed (count + 1) le_rfl

end Bandits.Support.ReferenceOccupiedFieldHistory

end
