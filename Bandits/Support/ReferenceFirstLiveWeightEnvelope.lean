/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLiveDispatchDomains

import Lean.Elab.Tactic.Omega
import Mathlib.Data.List.TakeWhile
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# First-live physical score and weight envelope

The physical source updates each complement score by its actual capped service
in `sources/zip4/manuscript/04_slow_fast_learner.tex:157-174,219-241`.
The initial all-one weights and zero score/queue seed come from the actual
first installation in `sources/zip4/manuscript/06_interruptions.tex:40-61`;
the clipped grid clock is specified at `:9-14,246-267`. Local numerical
failures and absorbing behavior are specified in
`sources/zip4/manuscript/appendix_a_local_protocol.tex:6-14,28-53`.

These results concern only the actual first physical episode. They do not
replay a hypothesized logical queue run or establish recorder, follower,
collection, later-episode, stability, probability, or regret closure.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceAssignmentPayloadChronology
open Bandits.Support.ReferenceFirstComplementMassBudget
open Bandits.Support.ReferenceFirstLiveConfirmationHistory
open Bandits.Support.ReferenceRunClockPreservation
open Bandits.Support.CoordinatorRoundDispatch
open Bandits.Support.CoordinatorLiveChoiceRecorderStep
open Bandits.Support.CoordinatorLiveServiceFinish
open Bandits.Support.CoordinatorPhaseClock
open Bandits.Support.ReferenceCoordinatorClockDomains
open Bandits.Support.ReplayWeightStability
open Bandits.Support.ScoreWeights
open Bandits.Support.FollowerCutoffScan

namespace Bandits.Support.ReferenceFirstLiveWeightEnvelope

abbrev Parameters := ReferenceFirstLiveDispatchDomains.Parameters
abbrev RateInput := ReferenceFirstLiveDispatchDomains.RateInput

variable {p : Parameters} {rate : RateInput p}

private def firstScoreCapInvariant (k : ℕ)
    (state : ReferenceActivePhysicalHorizon.State p rate) : Prop :=
  match state.coordinator with
  | .first => k = 0
  | .collection _ _ _ => False
  | .dagger => True
  | .live r _ _ =>
      (∀ a : Fin p.K, r.payload.anchor a = 1) ∧
      r.payload.n = rate.n ∧
      ∀ a : CanonicalFastSampling.FastArm r.payload.slowSet,
        r.complementScores a ≤ 4 * rate.n * k

private theorem firstWindow_record_eq_actualRunRecordAt
    (initial : ReferenceActivePhysicalHorizon.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (J : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (active : allActiveAtStart initial start)
    (hfirst : initial.coordinator = .first)
    (k : ℕ) (hkcount : k < count)
    (hkwindow : k <
      (ReferenceFirstComplementMassBudget.firstWindow initial rows J rewards
        start count hspan active).length) :
    (ReferenceFirstComplementMassBudget.firstWindow initial rows J rewards
      start count hspan active)[k] =
      ReferenceAssignmentPayloadChronology.actualRunRecordAt
        initial rows J rewards start k (by omega) active := by
  let E := ReferenceFirstComplementMassBudget.originalRun initial rows J rewards
    start count hspan active
  let W := ReferenceFirstComplementMassBudget.firstWindow initial rows J rewards
    start count hspan active
  have hseed : ReferenceCoordinatorClockDomains.clockAt rows J start initial := by
    simp [ReferenceCoordinatorClockDomains.clockAt, hfirst]
  have hclock := ReferenceRunClockPreservation.run_clockAt initial rows J rewards
    start count hspan active hseed
  have hwindowPrefix : W.IsPrefix E.records := by
    exact List.takeWhile_prefix _
  have hkE : k < E.records.length := by
    exact lt_of_lt_of_le hkwindow hwindowPrefix.length_le
  have hwindowElem : W[k] = E.records[k] := hwindowPrefix.getElem hkwindow
  have htimeMap := hclock.2.2.1
  have hkMap : k <
      (E.records.map (fun record => record.input.time.val)).length := by
    simpa using hkE
  have htimeElem :
      (E.records.map (fun record => record.input.time.val))[k] = W[k].input.time.val := by
    calc
      (E.records.map (fun record => record.input.time.val))[k] = E.records[k].input.time.val := by
        simp
      _ = W[k].input.time.val := by rw [← hwindowElem]
  have hwindowTime : W[k].input.time.val = start + k := by
    have htimeMap' : E.records.map (fun record => record.input.time.val) =
        ReferenceActivePhysicalHorizon.calendar start count := by
      simpa [E, ReferenceFirstComplementMassBudget.originalRun] using htimeMap
    have hkCalendar : k <
        (ReferenceActivePhysicalHorizon.calendar start count).length := by
      simpa [ReferenceActivePhysicalHorizon.calendar] using hkcount
    have hmapElem :
        (E.records.map (fun record => record.input.time.val))[k] =
          (ReferenceActivePhysicalHorizon.calendar start count)[k] := by
      exact List.getElem_of_eq htimeMap' hkMap
    have hcalendar :
        (ReferenceActivePhysicalHorizon.calendar start count)[k] = start + k := by
      simp [ReferenceActivePhysicalHorizon.calendar]
    calc
      W[k].input.time.val = (E.records.map (fun record => record.input.time.val))[k] :=
        htimeElem.symm
      _ = (ReferenceActivePhysicalHorizon.calendar start count)[k] := hmapElem
      _ = start + k := hcalendar
  let prefixRun := ReferenceFirstComplementMassBudget.originalPrefix
    initial rows J rewards start count hspan active (k + 1) (by omega)
  let actual := ReferenceAssignmentPayloadChronology.actualRunRecordAt
    initial rows J rewards start k (by omega) active
  have hprefixRecords : ∃ suffix, E.records = prefixRun.records ++ suffix := by
    obtain ⟨suffix, hrecords⟩ :=
      ReferenceCollectionPhaseHistory.run_records_prefix initial rows J rewards
        start (k + 1) (count - (k + 1)) (by omega) active
    refine ⟨suffix, ?_⟩
    have hkNext : k + 1 ≤ count := by omega
    simpa [E, prefixRun, ReferenceFirstComplementMassBudget.originalRun,
      ReferenceFirstComplementMassBudget.originalPrefix, Nat.add_sub_of_le hkNext] using hrecords
  obtain ⟨suffix, hrecords⟩ := hprefixRecords
  have hsuccessor := ReferenceAssignmentPayloadChronology.run_successor_actualRunRecordAt
    initial rows J rewards start k (by omega) active
  have hactualMemPrefix : actual ∈ prefixRun.records := by
    rw [hsuccessor]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  have hactualMemE : actual ∈ E.records := by
    rw [hrecords]
    exact List.mem_append_left _ hactualMemPrefix
  have hwindowMemE : W[k] ∈ E.records := by
    rw [hwindowElem]
    exact List.getElem_mem hkE
  have hactualTime : actual.input.time.val = start + k := rfl
  exact ReferenceAssignmentPayloadChronology.run_records_time_injective
    initial rows J rewards start count hspan active hwindowMemE hactualMemE
    (hwindowTime.trans hactualTime.symm)

private theorem livePostChoice_score_cap
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ) (started : CoordinatorPhaseClock.StartRoundResult p)
    (k : ℕ)
    (hanchor : ∀ a : Fin p.K, r.payload.anchor a = 1)
    (hn : r.payload.n = rate.n)
    (hscore : ∀ a : CanonicalFastSampling.FastArm r.payload.slowSet,
      r.complementScores a ≤ 4 * rate.n * k)
    (recording : CoordinatorRecordingOperation.Output p)
    (hrecorded : CoordinatorRecorderComplementBridge.run
      (ReferenceActivePhysicalStep.liveRecordingInput prepared r started) = some recording)
    (serviced : CoordinatorLiveServiceFinish.ServicedRegisters r q)
    (hservice : CoordinatorLiveServiceFinish.servicePass r q recording = .ok serviced)
    (next : ReferenceActivePhysicalHorizon.State p rate)
    (hnext : next.coordinator =
      (ReferenceActivePhysicalStep.livePostChoice prepared r q base started).configuration) :
    firstScoreCapInvariant (k + 1) next := by
  cases hconfirmation : CoordinatorLocalArmChoice.confirmationUpdate r.payload started.pending
      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
      x.time x.row prepared.coordinatorObservation with
  | none =>
      have hdagger : next.coordinator = .dagger := by
        calc
          next.coordinator =
              (ReferenceActivePhysicalStep.livePostChoice prepared r q base started).configuration := hnext
          _ = .dagger := by
            simp [ReferenceActivePhysicalStep.livePostChoice, hrecorded, hservice,
              hconfirmation, ReferenceActivePhysicalStep.coordinatorFailure]
      simp [firstScoreCapInvariant, hdagger]
  | some pending =>
      cases hfinish : CoordinatorPhaseClock.finishRound p rate.eta.val x.time started.clock
          pending x.row with
      | error failure =>
          have hdagger : next.coordinator = .dagger := by
            calc
              next.coordinator =
                  (ReferenceActivePhysicalStep.livePostChoice prepared r q base started).configuration := hnext
              _ = .dagger := by
                simp [ReferenceActivePhysicalStep.livePostChoice, hrecorded, hservice,
                  hconfirmation, hfinish, ReferenceActivePhysicalStep.coordinatorFailure,
                  CoordinatorLiveServiceFinish.finishFailureCode]
          simp [firstScoreCapInvariant, hdagger]
      | ok finished =>
          let nextRegisters : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta := {
            payload := r.payload
            priorClock := finished.clock
            pendingAtChoice := finished.pending
            time := x.time
            gridBoundary := finished.clock.g
            complementScores := serviced.score }
          let nextOwned : CoordinatorLiveServiceFinish.OwnedRegisters nextRegisters := {
            queue := serviced.queue
            previousService := serviced.previousService }
          have hconfiguration :
              (ReferenceActivePhysicalStep.livePostChoice prepared r q base started).configuration =
                .live nextRegisters nextOwned base := by
            simp [ReferenceActivePhysicalStep.livePostChoice, hrecorded, hservice,
              hconfirmation, hfinish, nextRegisters, nextOwned]
          have hpayload : nextRegisters.payload = r.payload := by
            have hframe := ReferenceAssignmentPayloadPersistence.livePostChoice_payload_frame
              prepared r q base started
            rw [hconfiguration] at hframe
          have hnextLive : next.coordinator = .live nextRegisters nextOwned base :=
            hnext.trans hconfiguration
          simp only [firstScoreCapInvariant, hnextLive]
          refine ⟨?_, ?_, ?_⟩
          · intro a
            rw [hpayload]
            exact hanchor a
          · rw [hpayload]
            exact hn
          · intro a
            have hcapService : serviced.service a ≤ 4 * r.payload.n := by
              rw [serviced.service_eq a]
              exact CappedService.service_le_capacity _ _ _
            have hnewScore : serviced.score a ≤ 4 * rate.n * (k + 1) := by
              rw [serviced.score_eq a]
              calc
                r.complementScores a + serviced.service a ≤
                    4 * rate.n * k + 4 * rate.n := Nat.add_le_add (hscore a) (by
                      simpa [hn] using hcapService)
                _ = 4 * rate.n * (k + 1) := by rw [Nat.mul_succ]
            simpa [nextRegisters] using hnewScore

private theorem run_first_live_score_cap
    (initial : ReferenceActivePhysicalHorizon.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (J : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (active : allActiveAtStart initial start)
    (hfirst : initial.coordinator = .first) :
    ∀ k (hkcount : k ≤ count)
      (_hkwindow : k ≤
        (ReferenceFirstComplementMassBudget.firstWindow initial rows J rewards
          start count hspan active).length),
      firstScoreCapInvariant k
        (ReferenceFirstComplementMassBudget.originalPrefix initial rows J rewards
          start count hspan active k hkcount).finalState := by
  intro k
  induction k with
  | zero =>
      intro hkcount hkwindow
      simp [firstScoreCapInvariant,
        ReferenceFirstComplementMassBudget.originalPrefix,
        ReferenceActivePhysicalHorizon.run_zero_final, hfirst]
  | succ k ih =>
      intro hkcount hkwindow
      have hkcountPrev : k ≤ count := by omega
      have hkwindowPrev : k ≤
          (ReferenceFirstComplementMassBudget.firstWindow initial rows J rewards
            start count hspan active).length := by omega
      let runPrefix := ReferenceFirstComplementMassBudget.originalPrefix
        initial rows J rewards start count hspan active k hkcountPrev
      let next := ReferenceFirstComplementMassBudget.originalPrefix
        initial rows J rewards start count hspan active (k + 1) hkcount
      have hInv : firstScoreCapInvariant k runPrefix.finalState := by
        simpa [runPrefix] using ih hkcountPrev hkwindowPrev
      let current :=
        (ReferenceFirstComplementMassBudget.firstWindow initial rows J rewards
          start count hspan active)[k]
      have hkltWindow : k <
          (ReferenceFirstComplementMassBudget.firstWindow initial rows J rewards
            start count hspan active).length := by omega
      have hcurrentEq : current =
          ReferenceAssignmentPayloadChronology.actualRunRecordAt
            initial rows J rewards start k (by omega) active := by
        exact firstWindow_record_eq_actualRunRecordAt initial rows J rewards
          start count hspan active hfirst k (by omega) hkltWindow
      have hstateIn : current.input.state = runPrefix.finalState := by
        rw [hcurrentEq]
        rfl
      have hstateOut : next.finalState = current.output.next := by
        calc
          next.finalState =
              (ReferenceAssignmentPayloadChronology.actualRunRecordAt
                initial rows J rewards start k (by omega) active).output.next :=
            ReferenceAssignmentPayloadChronology.run_successor_finalState_eq_actualRunRecordAt
              initial rows J rewards start k (by omega) active
          _ = current.output.next := by rw [hcurrentEq]
      have hcurrentMemWindow : current ∈
          ReferenceFirstComplementMassBudget.firstWindow initial rows J rewards
            start count hspan active :=
        List.getElem_mem (by omega)
      have hnotCut : ReferenceCollectionPhaseHistory.cutoffChosen current.input = false := by
        have hkeep := List.mem_takeWhile_imp hcurrentMemWindow
        simpa only [ReferenceFirstLiveConfirmationHistory.firstLiveWindow,
          Bool.not_eq_true'] using hkeep
      have hprepared : current.output.preparation =
          ReferenceActivePhysicalStep.prepare current.input := by
        rw [current.output_eq]
        rfl
      have hstepCoord : next.finalState.coordinator =
          current.output.preparation.observeCoordinator.configuration := by
        calc
          next.finalState.coordinator = current.output.next.coordinator :=
            congrArg (fun state : ReferenceActivePhysicalHorizon.State p rate => state.coordinator)
              hstateOut
          _ = (ReferenceActivePhysicalStep.step current.input).next.coordinator := by
            rw [current.output_eq]
          _ = (ReferenceActivePhysicalStep.prepare current.input).observeCoordinator.configuration :=
            (ReferenceActivePhysicalStep.step_next_fields current.input).1
          _ = current.output.preparation.observeCoordinator.configuration := by
            rw [← hprepared]
      cases hcoord : runPrefix.finalState.coordinator with
      | first =>
          simp only [firstScoreCapInvariant, hcoord] at hInv
          have hinputFirst : current.input.state.coordinator = .first := by
            rw [hstateIn, hcoord]
          have hprepEq : current.output.preparation.coordinator =
              .first (CoordinatorRoundDispatch.dispatchFirst
                (ReferenceActivePhysicalStep.firstInput current.input)) := by
            rw [hprepared]
            exact ReferenceActivePhysicalStep.dispatch_first current.input hinputFirst
          cases hdispatch : CoordinatorRoundDispatch.dispatchFirst
              (ReferenceActivePhysicalStep.firstInput current.input) with
          | choiceDomainFailure installed
          | recorderBoundaryFailure installed
          | choiceRejected installed =>
              have hselector :
                  (ReferenceActivePhysicalStep.DispatchCut.first
                    (CoordinatorRoundDispatch.dispatchFirst
                      (ReferenceActivePhysicalStep.firstInput current.input))).selection = none := by
                simp [hdispatch, ReferenceActivePhysicalStep.DispatchCut.selection]
              have hobs := ReferenceActivePhysicalStep.observeCoordinator_first_equation
                current.output.preparation
                (CoordinatorRoundDispatch.dispatchFirst
                  (ReferenceActivePhysicalStep.firstInput current.input)) hprepEq
              have hdagger : next.finalState.coordinator = .dagger := by
                calc
                  next.finalState.coordinator =
                      current.output.preparation.observeCoordinator.configuration := hstepCoord
                  _ = (ReferenceActivePhysicalStep.coordinatorFailure
                      current.input.state.upDecoderBank .dispatchRejected none none).configuration := by
                    rw [hobs]
                    simp [hselector]
                  _ = .dagger := rfl
              simp [firstScoreCapInvariant, next, hdagger]
          | chosen installed selection =>
              have hchosenTime := ReferenceActivePhysicalStep.dispatchFirst_chosen_time
                current.input installed selection hdispatch
              have hselector :
                  (ReferenceActivePhysicalStep.DispatchCut.first
                    (.chosen installed selection :
                      CoordinatorRoundDispatch.FirstOutcome
                        (ReferenceActivePhysicalStep.firstInput current.input))).selection ≠ none := by
                simp [ReferenceActivePhysicalStep.DispatchCut.selection,
                  ReferenceActivePhysicalStep.selectionAt, hchosenTime]
              have hprepChosen : current.output.preparation.coordinator =
                  .first (.chosen installed selection) := by
                rw [hprepared]
                calc
                  (ReferenceActivePhysicalStep.prepare current.input).coordinator =
                      ReferenceActivePhysicalStep.dispatch current.input := rfl
                  _ = .first (CoordinatorRoundDispatch.dispatchFirst
                      (ReferenceActivePhysicalStep.firstInput current.input)) :=
                    ReferenceActivePhysicalStep.dispatch_first current.input hinputFirst
                  _ = .first (.chosen installed selection) := by rw [hdispatch]
              have hobs := ReferenceActivePhysicalStep.observeCoordinator_first_equation
                current.output.preparation (.chosen installed selection) hprepChosen
              have htail : current.output.preparation.observeCoordinator =
                  ReferenceActivePhysicalStep.livePostChoice current.output.preparation
                    installed.registers installed.ownedRegisters
                    installed.followerBaseScore installed.startRoundResult := by
                rw [hobs]
                simp [hselector]
              have hnextTail : next.finalState.coordinator =
                  (ReferenceActivePhysicalStep.livePostChoice current.output.preparation
                    installed.registers installed.ownedRegisters installed.followerBaseScore
                    installed.startRoundResult).configuration :=
                hstepCoord.trans (congrArg CoordinatorObservation.configuration htail)
              have hseed := ReferenceActivePhysicalStep.dispatchFirst_zero_seed
                current.input installed selection hdispatch
              rcases hseed with ⟨hscore0, _, _, _⟩
              have hscoreOld : ∀ a, installed.registers.complementScores a ≤
                  4 * rate.n * k := by
                intro a
                rw [hscore0 a, hInv]
                simp
              have hanchor : ∀ a : Fin p.K,
                  installed.registers.payload.anchor a = 1 := by
                intro a
                have hinstall := ReferenceActivePhysicalStep.dispatchFirst_chosen_installation
                  current.input installed selection hdispatch
                rw [hinstall]
                exact CoordinatorAssignmentRegisterInstall.first_payload_anchor_one
                  (CoordinatorRoundDispatch.firstLaunchInput
                    (ReferenceActivePhysicalStep.firstInput current.input)) a
              have hn : installed.registers.payload.n = rate.n :=
                ReferenceActivePhysicalStep.payload_n_eq _
              let recordingInput := ReferenceActivePhysicalStep.liveRecordingInput
                current.output.preparation installed.registers installed.startRoundResult
              cases hrecorded : CoordinatorRecorderComplementBridge.run recordingInput with
              | none =>
                  have hdagger : next.finalState.coordinator = .dagger := by
                    calc
                      next.finalState.coordinator =
                          (ReferenceActivePhysicalStep.livePostChoice current.output.preparation
                            installed.registers installed.ownedRegisters
                            installed.followerBaseScore installed.startRoundResult).configuration :=
                        hnextTail
                      _ = .dagger := by
                        simp [ReferenceActivePhysicalStep.livePostChoice, recordingInput,
                          hrecorded, ReferenceActivePhysicalStep.coordinatorFailure]
                  simp [firstScoreCapInvariant, next, hdagger]
              | some recording =>
                  have hbudget := ReferenceFirstComplementMassBudget.run_first_service_pass_budget
                    initial rows J rewards start count hspan active hfirst ⟨k, by omega⟩
                  simp only [current, hprepChosen] at hbudget
                  have hserviceData := hbudget recording hrecorded
                  obtain ⟨serviced, hservice, _⟩ := hserviceData
                  exact livePostChoice_score_cap current.input current.output.preparation
                    installed.registers installed.ownedRegisters installed.followerBaseScore
                    installed.startRoundResult k hanchor hn hscoreOld recording hrecorded
                    serviced hservice next.finalState hnextTail
      | collection payload ledger savedProposal =>
          simp only [firstScoreCapInvariant, hcoord] at hInv
      | dagger =>
          have hinputDagger : current.input.state.coordinator = .dagger := by
            rw [hstateIn, hcoord]
          have hdagger : next.finalState.coordinator = .dagger := by
            calc
              next.finalState.coordinator =
                  current.output.preparation.observeCoordinator.configuration := hstepCoord
              _ = .dagger := by
                rw [hprepared]
                simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
                  ReferenceActivePhysicalStep.prepare, ReferenceActivePhysicalStep.dispatch,
                  hinputDagger, ReferenceActivePhysicalStep.DispatchCut.selection]
          simp [firstScoreCapInvariant, next, hdagger]
      | live oldRegisters oldOwned oldBase =>
          simp only [firstScoreCapInvariant, hcoord] at hInv
          rcases hInv with ⟨hanchorOld, hnOld, hscoreOld⟩
          have hinputLive : current.input.state.coordinator =
              .live oldRegisters oldOwned oldBase := by
            rw [hstateIn, hcoord]
          have hprepEq : current.output.preparation.coordinator =
              .live oldRegisters oldOwned oldBase
                (CoordinatorRoundDispatch.dispatchLive
                  (ReferenceActivePhysicalStep.liveInput current.input
                    oldRegisters oldOwned oldBase)) := by
            rw [hprepared]
            change ReferenceActivePhysicalStep.dispatch current.input =
              .live oldRegisters oldOwned oldBase
                (CoordinatorRoundDispatch.dispatchLive
                  (ReferenceActivePhysicalStep.liveInput current.input
                    oldRegisters oldOwned oldBase))
            rw [ReferenceActivePhysicalStep.dispatch, hinputLive]
            rfl
          let outcome := CoordinatorRoundDispatch.dispatchLive
            (ReferenceActivePhysicalStep.liveInput current.input
              oldRegisters oldOwned oldBase)
          have hobs := ReferenceActivePhysicalStep.observeCoordinator_live_equation
            current.output.preparation oldRegisters oldOwned oldBase outcome hprepEq
          cases hdispatch : outcome with
          | cutoffChosen dispatched hstart ledger hinit ledgerCandidate hvalid hclock hpending
              hassignment selection =>
              have hchosenCut : ReferenceCollectionPhaseHistory.cutoffChosen current.input = true := by
                have hdispatchLive : CoordinatorRoundDispatch.dispatchLive
                    (ReferenceActivePhysicalStep.liveInput current.input oldRegisters oldOwned oldBase) =
                      .cutoffChosen dispatched hstart ledger hinit ledgerCandidate hvalid hclock
                        hpending hassignment selection := by
                  simpa [outcome] using hdispatch
                unfold ReferenceCollectionPhaseHistory.cutoffChosen
                rw [← hprepared, hprepEq, hdispatchLive]
              simp [hchosenCut] at hnotCut
          | continuingChosen dispatched hstart continuation selection =>
              by_cases hselector :
                  (ReferenceActivePhysicalStep.DispatchCut.live oldRegisters oldOwned oldBase
                    outcome).selection = none
              · have hdagger : next.finalState.coordinator = .dagger := by
                  calc
                    next.finalState.coordinator =
                        current.output.preparation.observeCoordinator.configuration := hstepCoord
                    _ = (ReferenceActivePhysicalStep.coordinatorFailure
                        current.input.state.upDecoderBank .dispatchRejected none none).configuration := by
                      rw [hobs]
                      simp [hselector]
                    _ = .dagger := rfl
                simp [firstScoreCapInvariant, next, hdagger]
              · let actualRegisters :=
                  ReferenceActivePhysicalStep.liveRegistersAt oldRegisters current.input.time
                let actualOwned :=
                  ReferenceActivePhysicalStep.liveOwnedAt oldRegisters oldOwned current.input.time
                have hselectorChosen :
                    (ReferenceActivePhysicalStep.DispatchCut.live oldRegisters oldOwned oldBase
                      (.continuingChosen dispatched hstart continuation selection)).selection ≠ none := by
                  simpa [hdispatch] using hselector
                have htail : current.output.preparation.observeCoordinator =
                    ReferenceActivePhysicalStep.livePostChoice current.output.preparation
                      actualRegisters actualOwned oldBase dispatched.startResult := by
                  rw [hobs]
                  simp [hselectorChosen, hdispatch, actualRegisters, actualOwned]
                have hnextTail : next.finalState.coordinator =
                    (ReferenceActivePhysicalStep.livePostChoice current.output.preparation
                      actualRegisters actualOwned oldBase dispatched.startResult).configuration :=
                  hstepCoord.trans (congrArg CoordinatorObservation.configuration htail)
                have hanchor : ∀ a : Fin p.K,
                    actualRegisters.payload.anchor a = 1 := by
                  intro a
                  exact hanchorOld a
                have hn : actualRegisters.payload.n = rate.n := hnOld
                have hscore : ∀ a : CanonicalFastSampling.FastArm actualRegisters.payload.slowSet,
                    actualRegisters.complementScores a ≤
                    4 * rate.n * k := by
                  intro a
                  exact hscoreOld a
                let recordingInput := ReferenceActivePhysicalStep.liveRecordingInput
                  current.output.preparation actualRegisters dispatched.startResult
                cases hrecorded : CoordinatorRecorderComplementBridge.run recordingInput with
                | none =>
                    have hdagger : next.finalState.coordinator = .dagger := by
                      calc
                        next.finalState.coordinator =
                            (ReferenceActivePhysicalStep.livePostChoice current.output.preparation
                              actualRegisters actualOwned oldBase dispatched.startResult).configuration :=
                          hnextTail
                        _ = .dagger := by
                          simp [ReferenceActivePhysicalStep.livePostChoice, recordingInput,
                            hrecorded, ReferenceActivePhysicalStep.coordinatorFailure]
                    simp [firstScoreCapInvariant, next, hdagger]
                | some recording =>
                    have hbudget := ReferenceFirstComplementMassBudget.run_first_service_pass_budget
                      initial rows J rewards start count hspan active hfirst ⟨k, by omega⟩
                    simp only [current, hprepEq, outcome, hdispatch] at hbudget
                    have hserviceData := hbudget recording hrecorded
                    obtain ⟨serviced, hservice, _⟩ := hserviceData
                    exact livePostChoice_score_cap current.input current.output.preparation
                      actualRegisters actualOwned oldBase dispatched.startResult k hanchor hn hscore
                      recording hrecorded serviced hservice next.finalState hnextTail
          | clockFailure failure hfailure =>
              have hselector :
                  (ReferenceActivePhysicalStep.DispatchCut.live oldRegisters oldOwned oldBase
                    outcome).selection = none := by
                simp [ReferenceActivePhysicalStep.DispatchCut.selection, hdispatch]
              have hdagger : next.finalState.coordinator = .dagger := by
                calc
                  next.finalState.coordinator =
                      current.output.preparation.observeCoordinator.configuration := hstepCoord
                  _ = (ReferenceActivePhysicalStep.coordinatorFailure
                      current.input.state.upDecoderBank .dispatchRejected none none).configuration := by
                    rw [hobs]
                    simp [hselector]
                  _ = .dagger := rfl
              simp [firstScoreCapInvariant, next, hdagger]
          | initializerFailure dispatched hstart checked hchecked =>
              have hselector :
                  (ReferenceActivePhysicalStep.DispatchCut.live oldRegisters oldOwned oldBase
                    outcome).selection = none := by
                simp [ReferenceActivePhysicalStep.DispatchCut.selection, hdispatch]
              have hdagger : next.finalState.coordinator = .dagger := by
                calc
                  next.finalState.coordinator =
                      current.output.preparation.observeCoordinator.configuration := hstepCoord
                  _ = (ReferenceActivePhysicalStep.coordinatorFailure
                      current.input.state.upDecoderBank .dispatchRejected none none).configuration := by
                    rw [hobs]
                    simp [hselector]
                  _ = .dagger := rfl
              simp [firstScoreCapInvariant, next, hdagger]
          | localFailure dispatched hstart reason =>
              have hselector :
                  (ReferenceActivePhysicalStep.DispatchCut.live oldRegisters oldOwned oldBase
                    outcome).selection = none := by
                simp [ReferenceActivePhysicalStep.DispatchCut.selection, hdispatch]
              have hdagger : next.finalState.coordinator = .dagger := by
                calc
                  next.finalState.coordinator =
                      current.output.preparation.observeCoordinator.configuration := hstepCoord
                  _ = (ReferenceActivePhysicalStep.coordinatorFailure
                      current.input.state.upDecoderBank .dispatchRejected none none).configuration := by
                    rw [hobs]
                    simp [hselector]
                  _ = .dagger := rfl
              simp [firstScoreCapInvariant, next, hdagger]

private theorem first_live_elapsed_le_horizon
    (p : Parameters) (eta : ℝ) (start elapsed grid : ℕ)
    (hH : 0 < ReplayWeightStability.episodeHorizon eta)
    (hgrid : grid = min (p.T + 1)
      (ReplayWeightStability.episodeHorizon eta *
        ((start + 1) / ReplayWeightStability.episodeHorizon eta + 1)))
    (hbefore : start + elapsed < grid) :
    elapsed ≤ ReplayWeightStability.episodeHorizon eta := by
  let H := ReplayWeightStability.episodeHorizon eta
  have hrem : (start + 1) % H < H := Nat.mod_lt _ hH
  have hdiv : (start + 1) % H + H * ((start + 1) / H) = start + 1 :=
    Nat.mod_add_div _ _
  have hraw : H * ((start + 1) / H + 1) ≤ start + 1 + H := by
    rw [Nat.mul_succ]
    dsimp [H] at *
    omega
  have hrawBefore : start + elapsed <
      H * ((start + 1) / H + 1) := by
    have hmin : grid ≤ H * ((start + 1) / H + 1) := by
      rw [hgrid]
      exact Nat.min_le_right _ _
    exact lt_of_lt_of_le hbefore hmin
  dsimp [H] at *
  omega

private theorem live_weight_envelope_of_score_cap
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (k : ℕ) (hanchor : ∀ a : Fin p.K, r.payload.anchor a = 1)
    (hscore : ∀ a : CanonicalFastSampling.FastArm r.payload.slowSet,
      r.complementScores a ≤ 4 * rate.n * k)
    (hk : k ≤ ReplayWeightStability.episodeHorizon rate.eta.val) :
    r.complementEnvelopeValid := by
  have hD : 0 < (D p : ℝ) := by exact_mod_cast ConstructorDimensions.D_pos p
  have hDn : 0 < D p := ConstructorDimensions.D_pos p
  have heta : 0 < rate.eta.val := rate.eta.property
  have hnscale : (rate.n : ℝ) = rate.eta.val * (D p : ℝ) := rate.n_scale
  intro j
  have hweight : r.complementWeights j =
      Bandits.Support.ScoreWeights.scoreWeight
        (ReplayWeightStability.sourceBase (D p)) (r.complementScores j) := by
    rfl
  have hscoreReal : (r.complementScores j : ℝ) ≤
      4 * (rate.n : ℝ) * (k : ℝ) := by
    exact_mod_cast hscore j
  have hlog := Bandits.Support.ScoreWeightLogBounds.source_base_log_pow_le hD
    (r.complementScores j)
  have hlogBound :
      Real.log (Bandits.Support.ScoreWeights.scoreWeight
        (ReplayWeightStability.sourceBase (D p)) (r.complementScores j)) ≤
        4 * rate.eta.val * (k : ℝ) := by
    change Real.log ((1 + 1 / (D p : ℝ)) ^ (r.complementScores j)) ≤ _
    calc
      Real.log ((1 + 1 / (D p : ℝ)) ^ (r.complementScores j)) ≤
          (r.complementScores j : ℝ) / (D p : ℝ) := by
            simpa only [ReplayWeightStability.sourceBase, div_eq_mul_inv,
              mul_comm] using hlog
      _ ≤ (4 * (rate.n : ℝ) * (k : ℝ)) / (D p : ℝ) :=
            div_le_div_of_nonneg_right hscoreReal hD.le
      _ = 4 * rate.eta.val * (k : ℝ) := by
            rw [hnscale]
            field_simp [ne_of_gt hD]
  have hsmall : 4 * rate.eta.val * (k : ℝ) ≤ (1 : ℝ) / 16 := by
    have hkReal : (k : ℝ) ≤
        (ReplayWeightStability.episodeHorizon rate.eta.val : ℝ) :=
      Nat.cast_le.mpr hk
    calc
      4 * rate.eta.val * (k : ℝ) ≤
          4 * rate.eta.val *
            (ReplayWeightStability.episodeHorizon rate.eta.val : ℝ) :=
        mul_le_mul_of_nonneg_left hkReal (by positivity)
      _ ≤ 4 * rate.eta.val * (1 / (64 * rate.eta.val)) :=
        mul_le_mul_of_nonneg_left
          (ReplayWeightStability.episodeHorizon_cast_le heta) (by positivity)
      _ = (1 : ℝ) / 16 := by
        field_simp [ne_of_gt heta]
        norm_num
  have hlogTwo :
      Real.log (Bandits.Support.ScoreWeights.scoreWeight
        (ReplayWeightStability.sourceBase (D p)) (r.complementScores j)) ≤ Real.log 2 :=
    hlogBound.trans (hsmall.trans ReplayWeightStability.one_sixteenth_lt_log_two.le)
  have hpos := ReplayWeightStability.source_weight_pos (D := D p)
    (score := r.complementScores j) hDn
  have hupper : r.complementWeights j ≤ 2 := by
    rw [hweight]
    exact (Real.log_le_log_iff hpos (by norm_num)).mp hlogTwo
  have hlower : 1 ≤ r.complementWeights j := by
    rw [hweight]
    exact ScoreWeights.sourceWeight_mono hD (Nat.zero_le _)
  rw [hanchor j.1]
  constructor
  · exact hlower
  · simpa using hupper

/-! The theorem below uses the exact full input telescope of the admitted
first-live domain producer. The endpoint is the actual length-`k` physical
prefix; the inclusive window bound permits the prefix immediately before the
first chosen cutoff and never asks for a nonexistent terminal round. -/

/-- Every live endpoint in the computed FIRST physical window retains the
actual first all-one anchor and exact source numerator, and its actual
complement scores grow by at most the physical service cap `4*n` per completed
round. The source weight envelope follows from the clipped next-grid formula
and the literal source logarithm bound.

Source: `sources/zip4/manuscript/04_slow_fast_learner.tex:96-104,140-174,219-241`,
`sources/zip4/manuscript/06_interruptions.tex:9-14,40-70,246-267`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-53`. -/
theorem run_first_live_weight_envelope
    (initial : ReferenceActivePhysicalHorizon.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (J : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (active : allActiveAtStart initial start)
    (hfirst : initial.coordinator = .first) :
    ∀ k (hkcount : k ≤ count)
      (_hkwindow : k ≤
        (ReferenceFirstComplementMassBudget.firstWindow initial rows J rewards
          start count hspan active).length),
      match (ReferenceActivePhysicalHorizon.run initial rows J rewards
        start k (by omega) active).finalState.coordinator with
      | .live r _ _ =>
          (∀ a : Fin p.K, r.payload.anchor a = 1) ∧
          r.payload.n = rate.n ∧
          (∀ a : CanonicalFastSampling.FastArm r.payload.slowSet,
            r.complementScores a ≤ 4 * rate.n * k) ∧
          r.complementEnvelopeValid
      | _ => True := by
  intro k hkcount hkwindow
  have hcap := run_first_live_score_cap initial rows J rewards start count hspan active
    hfirst k hkcount hkwindow
  cases hcoord : (ReferenceActivePhysicalHorizon.run initial rows J rewards
      start k (by omega) active).finalState.coordinator with
  | first => trivial
  | collection payload ledger savedProposal => trivial
  | dagger => trivial
  | live r q base =>
      have hcapLive :
          (∀ a : Fin p.K, r.payload.anchor a = 1) ∧ r.payload.n = rate.n ∧
            ∀ a : CanonicalFastSampling.FastArm r.payload.slowSet,
              r.complementScores a ≤ 4 * rate.n * k := by
        simpa [firstScoreCapInvariant,
          ReferenceFirstComplementMassBudget.originalPrefix, hcoord] using hcap
      rcases hcapLive with ⟨hanchor, hn, hscore⟩
      have hclockSeed : ReferenceCoordinatorClockDomains.clockAt rows J start initial := by
        simp [ReferenceCoordinatorClockDomains.clockAt, hfirst]
      have hclock := ReferenceRunClockPreservation.run_clockAt initial rows J rewards
        start count hspan active hclockSeed
      have hclockPrefix := hclock.2.1 k hkcount
      have hclockLive : ReferenceCoordinatorClockDomains.clockAt rows J (start + k)
          (ReferenceActivePhysicalHorizon.run initial rows J rewards
            start k (by omega) active).finalState := by
        simpa using hclockPrefix
      simp only [ReferenceCoordinatorClockDomains.clockAt, hcoord] at hclockLive
      rcases hclockLive with ⟨_, hclockValid, hσ, _, hgrid, _hsourceBefore, hbeforeGrid, _⟩
      have hmass := ReferenceFirstComplementMassBudget.run_first_complement_mass
        initial rows J rewards start count hspan active hfirst k hkcount hkwindow
      dsimp [ReferenceFirstComplementMassBudget.originalPrefix] at hmass
      rw [hcoord] at hmass
      rcases hmass with ⟨_, _, _, birth, _, hbirth, hbirthTime⟩
      have hpayloadStart : r.payload.sigma.val = start := by
        exact (ReferenceAssignmentPayloadChronology.installationBirth_time_eq
          birth r.payload hbirth).trans hbirthTime
      have hgridFormula : r.gridBoundary = min (p.T + 1)
          (ReplayWeightStability.episodeHorizon rate.eta.val *
            ((r.payload.sigma.val + 1) /
              ReplayWeightStability.episodeHorizon rate.eta.val + 1)) := by
        have hsourceGrid := hclockValid.1
        rw [hσ, CoordinatorPhaseClock.boundaryFromSigma] at hsourceGrid
        calc
          r.gridBoundary = r.priorClock.g := hgrid
          _ = FollowerCutoffScan.gridBoundary p rate.eta.val r.payload.sigma := hsourceGrid
          _ = min (p.T + 1)
              (ReplayWeightStability.episodeHorizon rate.eta.val *
                ((r.payload.sigma.val + 1) /
                  ReplayWeightStability.episodeHorizon rate.eta.val + 1)) := by
                rfl
      have hH := FollowerCutoffScan.episodeHorizon_pos_of_source_cap
        p rate.eta.val rate.eta.property rate.sourceCap
      have hElapsed : k ≤ ReplayWeightStability.episodeHorizon rate.eta.val := by
        have hbefore : start + k < r.gridBoundary := by
          simpa [ReferenceCoordinatorClockDomains.clockAt, hcoord, hpayloadStart] using
            hbeforeGrid
        exact first_live_elapsed_le_horizon p rate.eta.val start k r.gridBoundary
          hH (by simpa [hpayloadStart] using hgridFormula) hbefore
      have henvelope := live_weight_envelope_of_score_cap r k hanchor hscore hElapsed
      exact ⟨hanchor, hn, hscore, henvelope⟩

/-- Before every actual next LIVE dispatch in the first physical window, the
incoming registers carry the produced source weight envelope, and the actual
dependent dispatcher chooses either its continuing or its checked cutoff
constructor. The cutoff input at the first chosen boundary is included when
it is still inside the physical run.

This result stops at pre-choice success. It does not assert recorder, follower
preparation, transport, confirmation, post-choice guard, later-episode, or
global no-dagger success.

Source: `sources/zip4/manuscript/04_slow_fast_learner.tex:96-104,140-174,219-241`,
`sources/zip4/manuscript/06_interruptions.tex:9-14,40-70,246-267`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:6-14,28-53`. -/
theorem run_first_live_prechoice_dispatch_success
    (initial : ReferenceActivePhysicalHorizon.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (J : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (active : allActiveAtStart initial start)
    (hfirst : initial.coordinator = .first) :
    ∀ k (hkcount : k < count)
      (_hkwindow : k ≤
        (ReferenceFirstComplementMassBudget.firstWindow initial rows J rewards
          start count hspan active).length),
      let record := ReferenceAssignmentPayloadChronology.actualRunRecordAt
        initial rows J rewards start k (by omega) active
      match record.input.state.coordinator with
      | .live r q base =>
          (ReferenceActivePhysicalStep.liveRegistersAt r record.input.time).complementEnvelopeValid ∧
          match CoordinatorRoundDispatch.dispatchLive
              (ReferenceActivePhysicalStep.liveInput record.input r q base) with
          | .continuingChosen .. => True
          | .cutoffChosen .. => True
          | _ => False
      | _ => True := by
  intro k hkcount hkwindow
  dsimp only
  generalize hrecord : ReferenceAssignmentPayloadChronology.actualRunRecordAt
      initial rows J rewards start k (by omega) active = record at ⊢
  have hdomainsRaw :=
    ReferenceFirstLiveDispatchDomains.run_first_live_initialization_domains
      initial rows J rewards start count hspan active hfirst k hkcount hkwindow
  have hcheckedRaw :=
    ReferenceFirstLiveDispatchDomains.run_first_live_start_round_dispatch_checked
      initial rows J rewards start count hspan active hfirst k hkcount hkwindow
  dsimp only at hdomainsRaw hcheckedRaw
  cases hcoord : record.input.state.coordinator with
  | first => trivial
  | collection payload ledger savedProposal => trivial
  | dagger => trivial
  | live r q base =>
      dsimp only
      let regs := ReferenceActivePhysicalStep.liveRegistersAt r record.input.time
      let owned := ReferenceActivePhysicalStep.liveOwnedAt r q record.input.time
      let x := ReferenceActivePhysicalStep.liveInput record.input r q base
      have hdomains :
          CoordinatorStartRoundCutoffDispatch.initializationDomainValid regs owned
            base record.input.time := by
        cases hrecord
        simpa [regs, owned, hcoord] using hdomainsRaw
      have hchecked : ∃ started,
          CoordinatorStartRoundCutoffDispatch.dispatch regs owned base =
            .ok ⟨started, .success
              (if started.ledgerCommand = some (.initializeAt record.input.time) then
                some (CoordinatorStartRoundCutoffDispatch.collectionStartLedger
                  regs owned base record.input.time)
              else none)⟩ := by
        cases hrecord
        simpa [regs, owned, hcoord] using hcheckedRaw
      let prefixRun := ReferenceFirstComplementMassBudget.originalPrefix
        initial rows J rewards start count hspan active k (Nat.le_of_lt hkcount)
      have hrecordState : record.input.state = prefixRun.finalState := by
        cases hrecord
        rfl
      have hprefixCoord : prefixRun.finalState.coordinator = .live r q base := by
        have hcoordState := congrArg
          (fun state : ReferenceActivePhysicalHorizon.State p rate => state.coordinator)
          hrecordState
        exact hcoordState.symm.trans hcoord
      have henvelopeAll := run_first_live_weight_envelope initial rows J rewards
        start count hspan active hfirst k (Nat.le_of_lt hkcount) hkwindow
      rw [show (ReferenceActivePhysicalHorizon.run initial rows J rewards start k
          (by omega) active).finalState.coordinator = .live r q base by
            simpa [prefixRun, ReferenceFirstComplementMassBudget.originalPrefix] using hprefixCoord]
        at henvelopeAll
      rcases henvelopeAll with ⟨hanchor, _hn, _hscore, henvelope⟩
      have hactualEnvelope : regs.complementEnvelopeValid := by
        simpa [regs, ReferenceActivePhysicalStep.liveRegistersAt,
          CoordinatorLiveChoiceRecorderStep.Registers.complementEnvelopeValid,
          CoordinatorLiveChoiceRecorderStep.Registers.complementWeights] using henvelope
      have hseed : ReferenceCoordinatorClockDomains.clockAt rows J start initial := by
        simp [ReferenceCoordinatorClockDomains.clockAt, hfirst]
      have hclockRun := ReferenceRunClockPreservation.run_clockAt initial rows J rewards
        start count hspan active hseed
      have hclockPrefix := hclockRun.2.1 k (Nat.le_of_lt hkcount)
      have hinputTime : record.input.time.val = start + k := by
        cases hrecord
        rfl
      have hclockRecord : ReferenceCoordinatorClockDomains.clockAt rows J
          record.input.time.val record.input.state := by
        rw [hrecordState, hinputTime]
        exact hclockPrefix
      have hclockLive := hclockRecord
      simp only [ReferenceCoordinatorClockDomains.clockAt, hcoord] at hclockLive
      rcases hclockLive with ⟨_, hclockValid, hsigma, hu, hgrid, hsourceBefore,
        hnextGrid, _⟩
      have hdomainsValid := hdomains
      rcases hdomains with ⟨hpayloadClock, hgridDomain, _hsourceBeforeDomain,
        hnextGridDomain, hgridBound, _hpayloadQueues, hscoreDomain,
        hqueueDomain, hpreviousDomain, hbaseDomain, _hinputLedger, _hledger⟩
      have huRegs : regs.priorClock.u = none := by
        simpa [regs, ReferenceActivePhysicalStep.liveRegistersAt] using hu
      have htime : CoordinatorPhaseClock.startRoundTimeValid p regs.time
          regs.priorClock := by
        simp only [CoordinatorPhaseClock.startRoundTimeValid, hpayloadClock, huRegs]
        refine ⟨?_, ?_⟩
        · simpa [regs, ReferenceActivePhysicalStep.liveRegistersAt] using hsourceBefore
        · have htimeGrid : regs.time.val < regs.priorClock.g := by
            have hnext : record.input.time.val < regs.gridBoundary := by omega
            calc
              regs.time.val = record.input.time.val := by rfl
              _ < regs.gridBoundary := hnext
              _ = regs.priorClock.g := by simpa [regs] using hgridDomain
          simpa [FollowerCutoffScan.calendarRound] using
            (Nat.succ_le_of_lt htimeGrid)
      have hparam := ReferenceCoordinatorClockDomains.proposalParameterValid_of_rate rate
      have hweights : ∀ j, 0 < regs.complementWeights j ∧
          regs.payload.anchor j.1 ≤ regs.complementWeights j ∧
          regs.complementWeights j ≤ 2 * regs.payload.anchor j.1 := by
        intro j
        have hband := hactualEnvelope j
        have hanchorOne : regs.payload.anchor j.1 = 1 := by
          simpa [regs, ReferenceActivePhysicalStep.liveRegistersAt] using hanchor j.1
        have hpositiveBound : 1 ≤ regs.complementWeights j := by
          simpa [hanchorOne] using hband.1
        exact ⟨lt_of_lt_of_le (by norm_num) hpositiveBound, hband.1, hband.2⟩
      have hsourceLe :
          CoordinatorLocalArmChoice.assignmentStart regs.payload ≤
            CoordinatorLocalArmChoice.sourceRound regs.time := by
        change r.payload.sigma.val + 1 ≤ record.input.time.val + 1
        omega
      have hchoiceFor (u : Option (Fin p.T))
          (hcutoff : CoordinatorLocalArmChoice.assignmentStart regs.payload ≤
            CoordinatorLocalArmChoice.cutoffRound
              (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p u)) :
          CoordinatorLocalArmChoice.ChoiceInputsValid regs.payload
            (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p u) regs.time
            regs.complementWeights :=
        CoordinatorLocalArmChoice.choiceInputsValid_mk regs.payload
          (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p u) regs.time
          regs.complementWeights hsourceLe hcutoff hweights
      rcases hchecked with ⟨started, hdispatch⟩
      have hstart := CoordinatorRoundDispatch.cutoffDispatch_startResult_eq
        regs owned base ⟨started, .success
          (if started.ledgerCommand = some (.initializeAt record.input.time) then
            some (CoordinatorStartRoundCutoffDispatch.collectionStartLedger
              regs owned base record.input.time)
          else none)⟩ hdispatch
      change CoordinatorPhaseClock.startRound p rate.eta.val regs.time
        regs.priorClock regs.clockPending = .ok started at hstart
      have hclockBoundary : regs.gridBoundary = regs.priorClock.g := by
        exact hgridDomain
      by_cases hcommand : started.ledgerCommand = some (.initializeAt record.input.time)
      · have hshape := CoordinatorStartRoundCutoffDispatch.startRound_initializeAt_shape
          regs started hstart hcommand
        have hcutoffClock : started.clock.u = some regs.time := by
          have hu' := congrArg CoordinatorPhaseClock.ClockRegisters.u hshape.1
          simpa [regs] using hu'
        have hcutoffStart :
            CoordinatorLocalArmChoice.assignmentStart regs.payload ≤
              CoordinatorLocalArmChoice.cutoffRound
                (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p
                  started.clock.u) := by
          rw [hcutoffClock]
          simp only [CoordinatorLiveChoiceRecorderStep.cutoffRoundFromClock,
            CoordinatorLocalArmChoice.assignmentStart]
          change r.payload.sigma.val + 1 ≤ record.input.time.val + 1
          omega
        have hchoice := hchoiceFor started.clock.u hcutoffStart
        have hboundary : started.clock.g ≤ p.T + 1 := by
          have hg := congrArg CoordinatorPhaseClock.ClockRegisters.g hshape.1
          calc
            started.clock.g = regs.priorClock.g := by simpa [regs] using hg
            _ = regs.gridBoundary := hclockBoundary.symm
            _ ≤ p.T + 1 := hgridBound
        have hnonempty := CoordinatorLiveChoiceRecorderStep.coordinatorArmChoice_ne_none
          regs.payload started.pending
          (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
          regs.time regs.complementWeights x.row hchoice
        have hdispatchInit :=
          CoordinatorStartRoundCutoffDispatch.dispatch_initializeAt_success
            regs owned base started hstart hcommand hdomainsValid
        have hdispatchInitStruct :
            CoordinatorStartRoundCutoffDispatch.dispatch
                { payload := r.payload, priorClock := r.priorClock,
                  pendingAtChoice := r.pendingAtChoice, time := record.input.time,
                  gridBoundary := r.gridBoundary, complementScores := r.complementScores }
                { queue := q.queue, previousService := q.previousService } base =
              .ok ⟨started, .success (some
                (CoordinatorStartRoundCutoffDispatch.collectionStartLedger
                  { payload := r.payload, priorClock := r.priorClock,
                    pendingAtChoice := r.pendingAtChoice, time := record.input.time,
                    gridBoundary := r.gridBoundary, complementScores := r.complementScores }
                  { queue := q.queue, previousService := q.previousService } base
                  record.input.time))⟩ := by
          simpa [regs, owned, ReferenceActivePhysicalStep.liveRegistersAt,
            ReferenceActivePhysicalStep.liveOwnedAt] using hdispatchInit
        cases hselected : CoordinatorLocalArmChoice.coordinatorArmChoice regs.payload
            started.pending
            (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
            regs.time regs.complementWeights x.row with
        | none => exact False.elim (hnonempty hselected)
        | some arm =>
            constructor
            · exact hactualEnvelope
            · have hdispatchKnown :
                  CoordinatorStartRoundCutoffDispatch.dispatch
                    x.registers x.ownedRegisters x.followerBaseScore =
                    .ok ⟨started, .success (some
                      (CoordinatorStartRoundCutoffDispatch.collectionStartLedger
                        x.registers x.ownedRegisters x.followerBaseScore x.registers.time))⟩ := by
                simpa [x, ReferenceActivePhysicalStep.liveInput, regs, owned,
                  ReferenceActivePhysicalStep.liveRegistersAt,
                  ReferenceActivePhysicalStep.liveOwnedAt] using hdispatchInitStruct
              have hchoiceX :
                  CoordinatorLocalArmChoice.ChoiceInputsValid x.registers.payload
                    (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
                    x.registers.time x.registers.complementWeights := by
                change CoordinatorLocalArmChoice.ChoiceInputsValid regs.payload
                  (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
                  regs.time regs.complementWeights
                exact hchoice
              have hEnvelopeX : x.registers.complementEnvelopeValid := by
                change regs.complementEnvelopeValid
                exact hactualEnvelope
              have hselectedX :
                  CoordinatorLocalArmChoice.coordinatorArmChoice x.registers.payload
                    started.pending
                    (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
                    x.registers.time x.registers.complementWeights x.row = some arm := by
                change CoordinatorLocalArmChoice.coordinatorArmChoice regs.payload
                  started.pending
                  (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
                  regs.time regs.complementWeights x.row = some arm
                exact hselected
              dsimp only [x] at hchoiceX hEnvelopeX hselectedX
              cases hresult : CoordinatorRoundDispatch.dispatchLive
                  (ReferenceActivePhysicalStep.liveInput record.input r q base) with
              | continuingChosen _ _ _ _ => trivial
              | cutoffChosen _ _ _ _ _ _ _ _ _ _ => trivial
              | clockFailure _ _
              | initializerFailure _ _ _ _
              | localFailure _ _ _ =>
                  unfold CoordinatorRoundDispatch.dispatchLive at hresult
                  dsimp only at hresult
                  split at hresult
                  · rename_i failure hcall
                    have hcontra := hcall.symm.trans hdispatchKnown
                    cases hcontra
                  · rename_i actual hcall
                    have hactual : actual = ⟨started, .success (some
                        (CoordinatorStartRoundCutoffDispatch.collectionStartLedger
                          x.registers x.ownedRegisters x.followerBaseScore x.registers.time))⟩ :=
                      Except.ok.inj (hcall.symm.trans hdispatchKnown)
                    subst actual
                    simp [hchoiceX, hboundary, hEnvelopeX] at hresult
                    split at hresult
                    · rename_i hnone
                      exact False.elim (hnonempty hnone)
                    · cases hresult
      · have hnoCommand : ∀ time,
            started.ledgerCommand ≠ some (.initializeAt time) := by
          intro time htimeCommand
          have htimeEq := CoordinatorRoundDispatch.startRound_initializeAt_time
            regs.time time regs.priorClock regs.clockPending started hstart
            htimeCommand
          subst time
          exact hcommand htimeCommand
        have hdispatchNo := CoordinatorStartRoundCutoffDispatch.dispatch_no_initialization
          regs owned base started hstart hnoCommand
        have hdispatchNoStruct :
            CoordinatorStartRoundCutoffDispatch.dispatch
                { payload := r.payload, priorClock := r.priorClock,
                  pendingAtChoice := r.pendingAtChoice, time := record.input.time,
                  gridBoundary := r.gridBoundary, complementScores := r.complementScores }
                { queue := q.queue, previousService := q.previousService } base =
              .ok ⟨started, .success none⟩ := by
          simpa [regs, owned, ReferenceActivePhysicalStep.liveRegistersAt,
            ReferenceActivePhysicalStep.liveOwnedAt] using hdispatchNo
        have hframe :
            CoordinatorLiveChoiceRecorderStep.unchangedLiveClockFrame regs
              started := by
          have hsourceTest : ¬ CoordinatorPhaseClock.sourceStartTest
              regs.priorClock.sigma regs.priorClock.u regs.time regs.clockPending := by
            simpa [hpayloadClock, huRegs] using
              (CoordinatorPhaseClock.sourceStartTest_false_without_cutoff
                regs.payload.sigma regs.time regs.clockPending)
          have hclockValidRegs : CoordinatorPhaseClock.clockRegistersValid p
              rate.eta.val regs.priorClock := by
            simpa [regs, ReferenceActivePhysicalStep.liveRegistersAt] using hclockValid
          let unchanged : CoordinatorPhaseClock.StartRoundResult p := {
            clock := regs.priorClock
            gridDomain := CoordinatorPhaseClock.clockRegistersValid_gridDomain
              p rate.eta.val regs.priorClock hclockValid
            pending := regs.clockPending
            ledgerCommand := none
            assignmentStart := none }
          have hunchangedStart : CoordinatorPhaseClock.startRound p rate.eta.val
              regs.time regs.priorClock regs.clockPending = .ok unchanged := by
            classical
            unfold CoordinatorPhaseClock.startRound
            cases hdetect : CoordinatorPhaseClock.detectCutoff regs.priorClock regs.time with
            | error failure =>
                simp [CoordinatorPhaseClock.startRound, hparam, hclockValidRegs,
                  htime, hdetect] at hstart
            | ok decision =>
                cases decision with
                | cutoff sigma' hsigma' =>
                    obtain ⟨cutoffResult, hcutoffStart, _, _, hcutoffCommand, _⟩ :=
                      CoordinatorPhaseClock.startRound_cutoff_effect p rate.eta.val
                        regs.time sigma' regs.priorClock regs.clockPending hparam
                        hclockValidRegs htime hsigma' hdetect
                    have heq : cutoffResult = started :=
                      Except.ok.inj (hcutoffStart.symm.trans hstart)
                    subst cutoffResult
                    exact False.elim (hnoCommand regs.time hcutoffCommand)
                | noCutoff =>
                    simp [hparam, hclockValidRegs, htime, hsourceTest,
                      unchanged, ↓reduceIte, ↓reduceDIte]
                    rfl
          have hstartedEq : started = unchanged :=
            Except.ok.inj (hstart.symm.trans hunchangedStart)
          change started.clock = regs.priorClock ∧
            started.pending = regs.clockPending ∧
            started.ledgerCommand = none ∧ started.assignmentStart = none
          rw [hstartedEq]
          exact ⟨rfl, rfl, rfl, rfl⟩
        have hcutoffStart :
            CoordinatorLocalArmChoice.assignmentStart regs.payload ≤
              CoordinatorLocalArmChoice.cutoffRound
                (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p
                  started.clock.u) := by
          rw [hframe.1, huRegs]
          simp only [CoordinatorLiveChoiceRecorderStep.cutoffRoundFromClock,
            CoordinatorLocalArmChoice.assignmentStart]
          change r.payload.sigma.val + 1 ≤ p.T + 1
          exact Nat.add_le_add_right r.payload.sigma.isLt.le 1
        have hchoice := hchoiceFor started.clock.u hcutoffStart
        have hlive : CoordinatorLocalArmChoice.assignmentIsLive regs.payload
            (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
            regs.time := by
          refine ⟨hchoice.time.assignment_started, ?_⟩
          rw [hframe.1, huRegs]
          have hsentinel : CoordinatorLocalArmChoice.sourceRound regs.time ≤ p.T := by
            have ht := regs.time.isLt
            simp [CoordinatorLocalArmChoice.sourceRound] at ht ⊢
          have hsentinelStrict : CoordinatorLocalArmChoice.sourceRound regs.time < p.T + 1 := by
            omega
          rw [CoordinatorLiveChoiceRecorderStep.cutoffRoundFromClock]
          simp only [Option.elim_none]
          exact hsentinelStrict
        have hboundary : started.clock.g ≤ p.T + 1 := by
          calc
            started.clock.g = regs.priorClock.g :=
              congrArg CoordinatorPhaseClock.ClockRegisters.g hframe.1
            _ = regs.gridBoundary := hclockBoundary.symm
            _ ≤ p.T + 1 := hgridBound
        have hnonempty := CoordinatorLiveChoiceRecorderStep.coordinatorArmChoice_ne_none
          regs.payload started.pending
          (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
          regs.time regs.complementWeights x.row hchoice
        cases hselected : CoordinatorLocalArmChoice.coordinatorArmChoice regs.payload
            started.pending
            (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
            regs.time regs.complementWeights x.row with
        | none => exact False.elim (hnonempty hselected)
        | some arm =>
            constructor
            · exact hactualEnvelope
            · have hdispatchKnown :
                  CoordinatorStartRoundCutoffDispatch.dispatch
                    x.registers x.ownedRegisters x.followerBaseScore =
                    .ok ⟨started, .success none⟩ := by
                simpa [x, ReferenceActivePhysicalStep.liveInput, regs, owned,
                  ReferenceActivePhysicalStep.liveRegistersAt,
                  ReferenceActivePhysicalStep.liveOwnedAt] using hdispatchNoStruct
              have hframeX :
                  CoordinatorLiveChoiceRecorderStep.unchangedLiveClockFrame
                    x.registers started := by
                change CoordinatorLiveChoiceRecorderStep.unchangedLiveClockFrame regs started
                exact hframe
              have hpayloadX : x.registers.priorClock.sigma =
                  some x.registers.payload.sigma := by
                change regs.priorClock.sigma = some regs.payload.sigma
                exact hpayloadClock
              have hgridX : x.registers.gridBoundary = x.registers.priorClock.g := by
                change regs.gridBoundary = regs.priorClock.g
                exact hclockBoundary
              have hscoreX : x.registers.scoreDomainValid := by
                change regs.scoreDomainValid
                exact hscoreDomain
              have hqueueX : x.ownedRegisters.queueDomainValid := by
                change owned.queueDomainValid
                exact hqueueDomain
              have hpreviousX : x.ownedRegisters.previousServiceDomainValid := by
                change owned.previousServiceDomainValid
                exact hpreviousDomain
              have hbaseX : ∀ i, x.followerBaseScore i ≤ p.T * D p := by
                change ∀ i, base i ≤ p.T * D p
                exact hbaseDomain
              have hliveX : CoordinatorLocalArmChoice.assignmentIsLive
                  x.registers.payload
                  (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
                  x.registers.time := by
                change CoordinatorLocalArmChoice.assignmentIsLive regs.payload
                  (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u) regs.time
                exact hlive
              have hchoiceX :
                  CoordinatorLocalArmChoice.ChoiceInputsValid x.registers.payload
                    (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
                    x.registers.time x.registers.complementWeights := by
                change CoordinatorLocalArmChoice.ChoiceInputsValid regs.payload
                  (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
                  regs.time regs.complementWeights
                exact hchoice
              have hEnvelopeX : x.registers.complementEnvelopeValid := by
                change regs.complementEnvelopeValid
                exact hactualEnvelope
              have hselectedX :
                  CoordinatorLocalArmChoice.coordinatorArmChoice x.registers.payload
                    started.pending
                    (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
                    x.registers.time x.registers.complementWeights x.row = some arm := by
                change CoordinatorLocalArmChoice.coordinatorArmChoice regs.payload
                  started.pending
                  (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
                  regs.time regs.complementWeights x.row = some arm
                exact hselected
              dsimp only [x] at hframeX hpayloadX hgridX hscoreX hqueueX hpreviousX hbaseX hliveX hchoiceX hEnvelopeX hselectedX
              cases hresult : CoordinatorRoundDispatch.dispatchLive
                  (ReferenceActivePhysicalStep.liveInput record.input r q base) with
              | continuingChosen _ _ _ _ => trivial
              | cutoffChosen _ _ _ _ _ _ _ _ _ _ => trivial
              | clockFailure _ _
              | initializerFailure _ _ _ _
              | localFailure _ _ _ =>
                  unfold CoordinatorRoundDispatch.dispatchLive at hresult
                  dsimp only at hresult
                  split at hresult
                  · rename_i failure hcall
                    have hcontra := hcall.symm.trans hdispatchKnown
                    cases hcontra
                  · rename_i actual hcall
                    have hactual : actual = ⟨started, .success none⟩ :=
                      Except.ok.inj (hcall.symm.trans hdispatchKnown)
                    subst actual
                    simp [hframeX, hpayloadX, hgridX, hscoreX, hqueueX,
                      hpreviousX, hbaseX, hliveX, hchoiceX, hboundary, hEnvelopeX] at hresult
                    split at hresult
                    · rename_i hnone
                      exact False.elim (hnonempty hnone)
                    · cases hresult

end Bandits.Support.ReferenceFirstLiveWeightEnvelope

end
