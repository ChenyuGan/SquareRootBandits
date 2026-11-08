/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceRunClockPreservation
public import Bandits.Support.ReferenceCoordinatorLiveRecording
public import Bandits.Support.ReferenceAssignmentPayloadChronology
public import Bandits.Support.ReferenceFirstLiveConfirmationHistory

import Lean.Elab.Tactic.Omega
import Mathlib.Data.List.TakeWhile

/-!
# First-assignment complement mass budget

Sources: `sources/zip4/manuscript/appendix_a_local_protocol.tex:28-53`,
`sources/zip4/manuscript/06_interruptions.tex:46-61,246-267,294-295`, and
`sources/zip4/manuscript/04_slow_fast_learner.tex:143-175`.

The prefix statements below use the actual finite physical run and its
first-live `takeWhile` window. The first chosen assignment has its literal
zero seed; each continuing live call passes the actual checked service guards
from complement mass plus the one recorder arrival. Failures, including the
absorbing coordinator dagger, remain the transitions of the original run.
This producer covers only the first assignment before the first chosen
coordinator cutoff. It does not establish returned mass through collection,
later assignment installation, global recorder truth, stability, or regret.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.CoordinatorRoundDispatch
open Bandits.Support.CoordinatorLiveChoiceRecorderStep
open Bandits.Support.ActiveRoundActions
open Bandits.Support.PublicDiscreteDraws
open Bandits.Support.CoordinatorLiveServiceFinish
open Bandits.Support.CoordinatorRecorderComplementBridge
open Bandits.Support.CoordinatorRecordingOperation
open Bandits.Support.ActiveFollowerDownAcceptance
open Bandits.Support.CanonicalFastSampling
open Bandits.Support.ReferenceAssignmentPayloadChronology
open Bandits.Support.ReferenceFirstLiveConfirmationHistory

namespace Bandits.Support.ReferenceFirstComplementMassBudget

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev Record (p : Parameters) (rate : RateInput p) :=
  ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)

variable {p : Parameters} {rate : RateInput p}

abbrev originalRun (initial : ReferenceActivePhysicalHorizon.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (J : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (active : allActiveAtStart initial start) :=
  ReferenceActivePhysicalHorizon.run initial rows J rewards start count hspan active

abbrev firstWindow (initial : ReferenceActivePhysicalHorizon.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (J : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (active : allActiveAtStart initial start) :=
  ReferenceFirstLiveConfirmationHistory.firstLiveWindow
    (originalRun initial rows J rewards start count hspan active).records

abbrev originalPrefix (initial : ReferenceActivePhysicalHorizon.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (J : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (active : allActiveAtStart initial start) (k : ℕ) (hk : k ≤ count) :=
  ReferenceActivePhysicalHorizon.run initial rows J rewards start k (by omega) active

/-- The induction datum is stated on one actual original-run prefix. A live
payload retains the actual first birth record; a later equal-start replacement
is not used to identify it. -/
private def firstMassInvariant (start k : ℕ) (records : List (Record p rate))
    (state : ReferenceActivePhysicalHorizon.State p rate) : Prop :=
  match state.coordinator with
  | .first => k = 0
  | .collection _ _ _ => False
  | .dagger => True
  | .live r q base =>
      (∀ a, r.complementScores a + q.queue a ≤ k * D p) ∧
      (∀ a, q.previousService a ≤ D p) ∧
      (∀ i, base i = 0) ∧
      ∃ birth, birth ∈ records ∧
        ReferenceAssignmentPayloadPersistence.InstallationBirth birth r.payload ∧
        birth.input.time.val = start

private theorem servicePass_of_prefix_mass
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (recording : CoordinatorRecordingOperation.Output p) (k : ℕ)
    (hmass : ∀ a, r.complementScores a + q.queue a ≤ k * D p)
    (hprevious : ∀ a, q.previousService a ≤ D p)
    (hk : k + 1 ≤ p.T) :
    ∃ serviced,
      CoordinatorLiveServiceFinish.servicePass r q recording = .ok serviced ∧
      (∀ a, serviced.score a + serviced.queue a ≤ (k + 1) * D p) ∧
      (∀ a, serviced.previousService a ≤ D p) := by
  classical
  let arrival : FastArm r.payload.slowSet → ℕ :=
    fun a => CoordinatorLiveServiceFinish.complementArrival r.payload recording a
  let service : FastArm r.payload.slowSet → ℕ :=
    fun a => CappedService.service (4 * r.payload.n) (q.queue a) (arrival a)
  let residual : FastArm r.payload.slowSet → ℕ :=
    fun a => CappedService.residual (4 * r.payload.n) (q.queue a) (arrival a)
  let score : FastArm r.payload.slowSet → ℕ :=
    fun a => r.complementScores a + service a
  have hkT : k ≤ p.T := by omega
  have hmassT : k * D p ≤ p.T * D p := Nat.mul_le_mul_right (D p) hkT
  have hqueueIn : q.queueDomainValid := by
    intro a
    have hle : q.queue a ≤ k * D p := by
      exact (Nat.le_add_left (q.queue a) (r.complementScores a)).trans (hmass a)
    exact hle.trans hmassT
  have hpreviousIn : q.previousServiceDomainValid := hprevious
  have harrival : ∀ a, arrival a ≤ D p := by
    intro a
    change (if recording.gateArm = some a.1 then recording.rawArrival else 0) ≤ D p
    by_cases hgate : recording.gateArm = some a.1
    · simp [hgate, recording.rawArrival_le_D]
    · simp [hgate]
  have hcap : 4 * r.payload.n ≤ D p := by
    rw [ReferenceActivePhysicalStep.payload_n_eq]
    exact ActiveFollowerDownAcceptance.four_n_le_D p rate
  have hservice : ∀ a, service a ≤ D p := by
    intro a
    exact (CappedService.service_le_capacity (4 * r.payload.n) (q.queue a)
      (arrival a)).trans hcap
  have hadvance : k * D p + D p = (k + 1) * D p := by
    rw [Nat.add_mul, one_mul]
  have hscoreMass : ∀ a,
      score a + residual a ≤ (k + 1) * D p := by
    intro a
    have hconservation :
        score a + residual a =
          r.complementScores a + q.queue a + arrival a := by
      dsimp [score, service, residual]
      calc
        r.complementScores a +
            CappedService.service (4 * r.payload.n) (q.queue a) (arrival a) +
            CappedService.residual (4 * r.payload.n) (q.queue a) (arrival a) =
          r.complementScores a +
            (CappedService.residual (4 * r.payload.n) (q.queue a) (arrival a) +
              CappedService.service (4 * r.payload.n) (q.queue a) (arrival a)) := by omega
        _ = r.complementScores a + (q.queue a + arrival a) := by
          rw [CappedService.residual_add_service]
        _ = r.complementScores a + q.queue a + arrival a := by omega
    have hsum : r.complementScores a + q.queue a + arrival a ≤
        (k + 1) * D p := by
      calc
        r.complementScores a + q.queue a + arrival a ≤ k * D p + D p :=
          Nat.add_le_add (hmass a) (harrival a)
        _ = (k + 1) * D p := hadvance
    rw [hconservation]
    exact hsum
  have hscoreOut : ∀ a, score a ≤ p.T * D p := by
    intro a
    have h := hscoreMass a
    have hnext : (k + 1) * D p ≤ p.T * D p :=
      Nat.mul_le_mul_right (D p) hk
    dsimp [score] at h ⊢
    omega
  have hqueueOut : ∀ a, residual a ≤ p.T * D p := by
    intro a
    have hnext : (k + 1) * D p ≤ p.T * D p :=
      Nat.mul_le_mul_right (D p) hk
    exact (Nat.le_add_left (residual a) (score a)).trans
      ((hscoreMass a).trans hnext)
  let serviced : CoordinatorLiveServiceFinish.ServicedRegisters r q := {
    recording := recording
    arrival := arrival
    service := service
    queue := residual
    score := score
    previousService := service
    arrivalDomain := harrival
    serviceDomain := hservice
    queueDomain := hqueueOut
    scoreDomain := hscoreOut
    previousServiceDomain := hservice
    arrival_eq := fun _ => rfl
    service_eq := fun _ => rfl
    queue_eq := fun _ => rfl
    score_eq := fun _ => rfl
    previousService_eq := fun _ => rfl }
  have hpass : CoordinatorLiveServiceFinish.servicePass r q recording = .ok serviced := by
    unfold CoordinatorLiveServiceFinish.servicePass
    rw [dite_eq_left hqueueIn, dite_eq_left hpreviousIn]
    rw [dite_eq_left harrival, dite_eq_left hservice]
    rw [dite_eq_left hscoreOut, dite_eq_left hqueueOut]
  refine ⟨serviced, hpass, ?_, ?_⟩
  · intro a
    calc
      serviced.score a + serviced.queue a =
          r.complementScores a + q.queue a + arrival a :=
        CoordinatorLiveServiceFinish.serviced_conservation r q serviced a
      _ ≤ k * D p + D p := Nat.add_le_add (hmass a) (harrival a)
      _ = (k + 1) * D p := hadvance
  · intro a
    exact serviced.previousServiceDomain a

private theorem actualStepRecord_eq (record : Record p rate) :
    ReferenceAssignmentPayloadChronology.actualStepRecord record.input = record := by
  cases record with
  | mk input output houtput =>
    cases houtput
    rfl

/-- A retained first-live element is the same computed record as the
successor constructor of the original run. C supplies the calendar
coordinate, and B's injective actual-record timestamp supplies record identity. -/
private theorem firstWindow_record_eq_actualRunRecordAt
    (initial : ReferenceActivePhysicalHorizon.State p rate) (rows : CompletePublicTable.CompleteRows p)
    (J : Fin (M p)) (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (active : allActiveAtStart initial start) (hfirst : initial.coordinator = .first)
    (k : ℕ) (hkcount : k < count)
    (hkwindow : k < (firstWindow initial rows J rewards start count hspan active).length) :
    (firstWindow initial rows J rewards start count hspan active)[k] =
      ReferenceAssignmentPayloadChronology.actualRunRecordAt initial rows J rewards start k
        (by omega) active := by
  let E := originalRun initial rows J rewards start count hspan active
  let W := firstWindow initial rows J rewards start count hspan active
  have hseed : ReferenceCoordinatorClockDomains.clockAt rows J start initial := by
    simp [ReferenceCoordinatorClockDomains.clockAt, hfirst]
  have hclock := ReferenceRunClockPreservation.run_clockAt initial rows J rewards
    start count hspan active hseed
  have hwindowPrefix : W.IsPrefix E.records := by
    exact List.takeWhile_prefix _
  have hkE : k < E.records.length := by
    have hlen := hwindowPrefix.length_le
    exact lt_of_lt_of_le hkwindow hlen
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
    have htimeMap' :
        E.records.map (fun record => record.input.time.val) =
          ReferenceActivePhysicalHorizon.calendar start count := by
      simpa [E, originalRun] using htimeMap
    have hkCalendar : k < (ReferenceActivePhysicalHorizon.calendar start count).length := by
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
  let next := originalPrefix initial rows J rewards start count hspan active
    (k + 1) (by omega)
  let actual := ReferenceAssignmentPayloadChronology.actualRunRecordAt initial rows J rewards
    start k (by omega) active
  have hnextPrefix : ∃ suffix, E.records = next.records ++ suffix := by
    obtain ⟨suffix, hrecords⟩ := ReferenceCollectionPhaseHistory.run_records_prefix
      initial rows J rewards start (k + 1) (count - (k + 1)) (by omega) active
    refine ⟨suffix, ?_⟩
    have hkNext : k + 1 ≤ count := by omega
    simpa [E, next, originalRun, originalPrefix, Nat.add_sub_of_le hkNext] using hrecords
  obtain ⟨suffix, hrecords⟩ := hnextPrefix
  have hsuccessor := ReferenceAssignmentPayloadChronology.run_successor_actualRunRecordAt
    initial rows J rewards start k (by omega) active
  have hactualMemNext : actual ∈ next.records := by
    rw [hsuccessor]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  have hactualMemE : actual ∈ E.records := by
    rw [hrecords]
    exact List.mem_append_left _ hactualMemNext
  have hwindowMemE : W[k] ∈ E.records := by
    rw [hwindowElem]
    exact List.getElem_mem hkE
  have hactualTime : actual.input.time.val = start + k := by
    rfl
  exact ReferenceAssignmentPayloadChronology.run_records_time_injective
    initial rows J rewards start count hspan active hwindowMemE hactualMemE
    (hwindowTime.trans hactualTime.symm)

private theorem live_tail_prefix_mass
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (start k : ℕ) (recordsNext : List (Record p rate))
    (stateNext : ReferenceActivePhysicalHorizon.State p rate)
    (hmass : ∀ a, r.complementScores a + q.queue a ≤ k * D p)
    (hprevious : ∀ a, q.previousService a ≤ D p)
    (hbase : ∀ i, base i = 0)
    (birth : Record p rate)
    (hbirthMem : birth ∈ recordsNext)
    (hbirth : ReferenceAssignmentPayloadPersistence.InstallationBirth birth r.payload)
    (hbirthTime : birth.input.time.val = start)
    (recording : CoordinatorRecordingOperation.Output p)
    (hnext : stateNext.coordinator =
      (ReferenceActivePhysicalStep.livePostChoice prepared r q base started).configuration)
    (hrecorded : CoordinatorRecorderComplementBridge.run
      (ReferenceActivePhysicalStep.liveRecordingInput prepared r started) = some recording)
    (hk : k + 1 ≤ p.T) :
    firstMassInvariant start (k + 1) recordsNext stateNext := by
  obtain ⟨serviced, hservice, hmassNext, hpreviousNext⟩ :=
    servicePass_of_prefix_mass r q recording k hmass hprevious hk
  cases hconfirmation : CoordinatorLocalArmChoice.confirmationUpdate r.payload started.pending
      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
      x.time x.row prepared.coordinatorObservation with
  | none =>
      have hdagger : stateNext.coordinator = .dagger := by
        calc
          stateNext.coordinator =
              (ReferenceActivePhysicalStep.livePostChoice prepared r q base started).configuration := hnext
          _ = .dagger := by
            simp [ReferenceActivePhysicalStep.livePostChoice, hrecorded, hservice,
              hconfirmation, ReferenceActivePhysicalStep.coordinatorFailure]
      simp [firstMassInvariant, hdagger]
  | some pending =>
      cases hfinish : CoordinatorPhaseClock.finishRound p rate.eta.val x.time started.clock
          pending x.row with
      | error failure =>
          have hdagger : stateNext.coordinator = .dagger := by
            calc
              stateNext.coordinator =
                  (ReferenceActivePhysicalStep.livePostChoice prepared r q base started).configuration := hnext
              _ = .dagger := by
                simp [ReferenceActivePhysicalStep.livePostChoice, hrecorded, hservice,
                  hconfirmation, hfinish, ReferenceActivePhysicalStep.coordinatorFailure,
                  CoordinatorLiveServiceFinish.finishFailureCode]
          simp [firstMassInvariant, hdagger]
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
          have hnextLive : stateNext.coordinator = .live nextRegisters nextOwned base :=
            hnext.trans hconfiguration
          simp only [firstMassInvariant, hnextLive]
          refine ⟨?_, ?_, hbase, birth, hbirthMem, ?_, hbirthTime⟩
          · intro a
            simpa [nextRegisters, nextOwned] using hmassNext a
          · intro a
            simpa [nextRegisters, nextOwned] using hpreviousNext a
          · rw [hpayload]
            exact hbirth

private theorem run_first_mass_prefix
    (initial : ReferenceActivePhysicalHorizon.State p rate) (rows : CompletePublicTable.CompleteRows p)
    (J : Fin (M p)) (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (active : allActiveAtStart initial start) (hfirst : initial.coordinator = .first) :
    ∀ k (hkcount : k ≤ count)
      (_hkwindow : k ≤ (firstWindow initial rows J rewards start count hspan active).length),
      firstMassInvariant start k
        (originalPrefix initial rows J rewards start count hspan active k hkcount).records
        (originalPrefix initial rows J rewards start count hspan active k hkcount).finalState := by
  intro k
  induction k with
  | zero =>
      intro hkcount _
      simp [firstMassInvariant, originalPrefix,
        ReferenceActivePhysicalHorizon.run_zero_final, hfirst]
  | succ k ih =>
      intro hkcount _hkwindow
      have hkcountPrev : k ≤ count := Nat.le_trans (Nat.le_succ k) hkcount
      have hkwindowPrev : k ≤
          (firstWindow initial rows J rewards start count hspan active).length :=
        Nat.le_trans (Nat.le_succ k) _hkwindow
      let runPrefix := originalPrefix initial rows J rewards start count hspan active k hkcountPrev
      let next := originalPrefix initial rows J rewards start count hspan active (k + 1) hkcount
      have hInv : firstMassInvariant start k runPrefix.records runPrefix.finalState := by
        simpa [runPrefix] using ih hkcountPrev hkwindowPrev
      let current :=
        (firstWindow initial rows J rewards start count hspan active)[k]
      have hcurrentEq : current =
          ReferenceAssignmentPayloadChronology.actualRunRecordAt initial rows J rewards
            start k (by omega) active := by
        exact firstWindow_record_eq_actualRunRecordAt initial rows J rewards start count
          hspan active hfirst k (by omega) (by omega)
      have htimeCurrent : current.input.time.val = start + k := by
        rw [hcurrentEq]
        rfl
      have hstateIn : current.input.state = runPrefix.finalState := by
        rw [hcurrentEq]
        rfl
      have hstateOut : next.finalState = current.output.next := by
        calc
          next.finalState =
              (ReferenceAssignmentPayloadChronology.actualRunRecordAt initial rows J rewards
                start k (by omega) active).output.next :=
            ReferenceAssignmentPayloadChronology.run_successor_finalState_eq_actualRunRecordAt
              initial rows J rewards start k (by omega) active
          _ = current.output.next := by rw [hcurrentEq]
      have hcurrentMemWindow : current ∈
          firstWindow initial rows J rewards start count hspan active :=
        List.getElem_mem
          (lt_of_lt_of_le (Nat.lt_succ_self k) _hkwindow)
      have hnotCut : ReferenceCollectionPhaseHistory.cutoffChosen current.input = false := by
        have hkeep := List.mem_takeWhile_imp hcurrentMemWindow
        simpa only [ReferenceFirstLiveConfirmationHistory.firstLiveWindow,
          Bool.not_eq_true'] using hkeep
      have hcurrentMemNext : current ∈ next.records := by
        rw [hcurrentEq,
          ReferenceAssignmentPayloadChronology.run_successor_actualRunRecordAt
            initial rows J rewards start k (by omega) active]
        exact List.mem_append_right _ (List.mem_singleton_self _)
      have hprepared : current.output.preparation =
          ReferenceActivePhysicalStep.prepare current.input := by
        rw [current.output_eq]
        rfl
      have hstepCoord : next.finalState.coordinator =
          current.output.preparation.observeCoordinator.configuration := by
        calc
          next.finalState.coordinator = current.output.next.coordinator :=
            congrArg (fun state : ReferenceActivePhysicalHorizon.State p rate => state.coordinator) hstateOut
          _ = (ReferenceActivePhysicalStep.step current.input).next.coordinator := by
            rw [current.output_eq]
          _ = (ReferenceActivePhysicalStep.prepare current.input).observeCoordinator.configuration :=
            (ReferenceActivePhysicalStep.step_next_fields current.input).1
          _ = current.output.preparation.observeCoordinator.configuration := by
            rw [← hprepared]
      cases hcoord : runPrefix.finalState.coordinator with
      | first =>
          simp only [firstMassInvariant, hcoord] at hInv
          have hinputFirst : current.input.state.coordinator = .first := by
            rw [hstateIn, hcoord]
          have hprepEq : current.output.preparation.coordinator =
              .first (CoordinatorRoundDispatch.dispatchFirst
                (ReferenceActivePhysicalStep.firstInput current.input)) := by
            rw [hprepared]
            exact (ReferenceActivePhysicalStep.dispatch_first current.input hinputFirst)
          cases hdispatch : CoordinatorRoundDispatch.dispatchFirst
              (ReferenceActivePhysicalStep.firstInput current.input) with
          | choiceDomainFailure installed =>
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
              simp [firstMassInvariant, next, hdagger]

          | recorderBoundaryFailure installed =>
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
              simp [firstMassInvariant, next, hdagger]
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
              simp [firstMassInvariant, next, hdagger]
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
                    installed.registers installed.ownedRegisters
                    installed.followerBaseScore installed.startRoundResult).configuration :=
                hstepCoord.trans (congrArg CoordinatorObservation.configuration htail)
              have hseed := ReferenceActivePhysicalStep.dispatchFirst_zero_seed
                current.input installed selection hdispatch
              rcases hseed with ⟨hscore0, hqueue0, hprevious0, hbase0⟩
              have hmass : ∀ a, installed.registers.complementScores a +
                  installed.ownedRegisters.queue a ≤ k * D p := by
                intro a
                rw [hscore0 a, hqueue0 a, hInv]
                simp
              let birth := ReferenceAssignmentPayloadChronology.actualStepRecord current.input
              have hbirth :
                  ReferenceAssignmentPayloadPersistence.InstallationBirth birth
                    installed.registers.payload :=
                ReferenceAssignmentPayloadChronology.actualFirstChosen_installationBirth
                  current.input hinputFirst installed selection hdispatch
              have hbirthEq : birth = current := by
                dsimp [birth]
                exact actualStepRecord_eq current
              have hbirthMemNext : birth ∈ next.records := by
                rw [hbirthEq]
                exact hcurrentMemNext
              have hbirthTimeCurrent : current.input.time.val = start := by
                omega
              have hbirthTime : birth.input.time.val = start := by
                simpa [birth, ReferenceAssignmentPayloadChronology.actualStepRecord]
                  using hbirthTimeCurrent
              have hpreviousBound :
                  ∀ a, installed.ownedRegisters.previousService a ≤ D p := by
                intro a
                rw [hprevious0 a]
                exact Nat.zero_le _
              cases hrecorded : CoordinatorRecorderComplementBridge.run
                  (ReferenceActivePhysicalStep.liveRecordingInput current.output.preparation
                    installed.registers installed.startRoundResult) with
              | none =>
                  have hdagger : next.finalState.coordinator = .dagger := by
                    simpa [ReferenceActivePhysicalStep.livePostChoice, hrecorded,
                      ReferenceActivePhysicalStep.coordinatorFailure] using hnextTail
                  simp [firstMassInvariant, next, hdagger]
              | some recording =>
                  exact live_tail_prefix_mass current.input current.output.preparation
                    installed.registers installed.ownedRegisters installed.followerBaseScore
                    installed.startRoundResult start k next.records next.finalState
                    hmass hpreviousBound hbase0 birth hbirthMemNext hbirth hbirthTime
                    recording hnextTail hrecorded (by omega)
      | collection payload ledger savedProposal =>
          simp only [firstMassInvariant, hcoord] at hInv
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
          simp [firstMassInvariant, next, hdagger]
      | live oldRegisters oldOwned oldBase =>
          simp only [firstMassInvariant, hcoord] at hInv
          rcases hInv with ⟨hmassOld, hpreviousOld, hbaseOld,
            birth, hbirthMem, hbirth, hbirthTime⟩
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
              have hchosenCut :
                  ReferenceCollectionPhaseHistory.cutoffChosen current.input = true := by
                have hdispatchLive : CoordinatorRoundDispatch.dispatchLive
                    (ReferenceActivePhysicalStep.liveInput current.input
                      oldRegisters oldOwned oldBase) =
                      .cutoffChosen dispatched hstart ledger hinit ledgerCandidate hvalid hclock
                        hpending hassignment selection := by
                  simpa [outcome] using hdispatch
                unfold ReferenceCollectionPhaseHistory.cutoffChosen
                rw [← hprepared, hprepEq, hdispatchLive]
              simp [hchosenCut] at hnotCut
          | continuingChosen dispatched hstart continuation selection =>
              by_cases hselector :
                  (ReferenceActivePhysicalStep.DispatchCut.live oldRegisters oldOwned
                    oldBase outcome).selection = none
              · have hdagger : next.finalState.coordinator = .dagger := by
                  calc
                    next.finalState.coordinator =
                        current.output.preparation.observeCoordinator.configuration := hstepCoord
                    _ = (ReferenceActivePhysicalStep.coordinatorFailure
                        current.input.state.upDecoderBank .dispatchRejected none none).configuration := by
                      rw [hobs]
                      simp [hselector]
                    _ = .dagger := rfl
                simp [firstMassInvariant, next, hdagger]
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
                have hmass : ∀ a, actualRegisters.complementScores a +
                    actualOwned.queue a ≤ k * D p := by
                  intro a
                  simpa [actualRegisters, actualOwned,
                    ReferenceActivePhysicalStep.liveRegistersAt,
                    ReferenceActivePhysicalStep.liveOwnedAt] using hmassOld a
                have hprevious : ∀ a, actualOwned.previousService a ≤ D p := by
                  intro a
                  simpa [actualRegisters, actualOwned,
                    ReferenceActivePhysicalStep.liveRegistersAt,
                    ReferenceActivePhysicalStep.liveOwnedAt] using hpreviousOld a
                have hbirthNext : birth ∈ next.records := by
                  rw [ReferenceAssignmentPayloadChronology.run_successor_actualRunRecordAt
                    initial rows J rewards start k (by omega) active]
                  exact List.mem_append_left _ hbirthMem
                cases hrecorded : CoordinatorRecorderComplementBridge.run
                    (ReferenceActivePhysicalStep.liveRecordingInput current.output.preparation
                      actualRegisters dispatched.startResult) with
                | none =>
                    have hdagger : next.finalState.coordinator = .dagger := by
                      simpa [ReferenceActivePhysicalStep.livePostChoice, hrecorded,
                        ReferenceActivePhysicalStep.coordinatorFailure] using hnextTail
                    simp [firstMassInvariant, next, hdagger]
                | some recording =>
                    exact live_tail_prefix_mass current.input current.output.preparation
                      actualRegisters actualOwned oldBase dispatched.startResult start k next.records
                      next.finalState hmass hprevious hbaseOld birth hbirthNext hbirth
                      hbirthTime recording hnextTail hrecorded (by omega)
          | clockFailure failure hfailure =>
              have hselector :
                  (ReferenceActivePhysicalStep.DispatchCut.live oldRegisters oldOwned
                    oldBase outcome).selection = none := by
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
              simp [firstMassInvariant, next, hdagger]
          | initializerFailure dispatched hstart checked hchecked =>
              have hselector :
                  (ReferenceActivePhysicalStep.DispatchCut.live oldRegisters oldOwned
                    oldBase outcome).selection = none := by
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
              simp [firstMassInvariant, next, hdagger]
          | localFailure dispatched hstart reason =>
              have hselector :
                  (ReferenceActivePhysicalStep.DispatchCut.live oldRegisters oldOwned
                    oldBase outcome).selection = none := by
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
              simp [firstMassInvariant, next, hdagger]

private theorem firstWindow_length_le_count
    (initial : ReferenceActivePhysicalHorizon.State p rate) (rows : CompletePublicTable.CompleteRows p)
    (J : Fin (M p)) (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (active : allActiveAtStart initial start) :
    (firstWindow initial rows J rewards start count hspan active).length ≤ count := by
  have hprefix :
      (firstWindow initial rows J rewards start count hspan active).IsPrefix
        (originalRun initial rows J rewards start count hspan active).records :=
    List.takeWhile_prefix _
  have hlen := hprefix.length_le
  dsimp [originalRun] at hlen
  rw [ReferenceActivePhysicalHorizon.run_record_count] at hlen
  exact hlen

private theorem firstWindow_input_state_eq_prefix
    (initial : ReferenceActivePhysicalHorizon.State p rate) (rows : CompletePublicTable.CompleteRows p)
    (J : Fin (M p)) (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (active : allActiveAtStart initial start) (hfirst : initial.coordinator = .first)
    (k : ℕ) (hkcount : k ≤ count)
    (hkwindow : k < (firstWindow initial rows J rewards start count hspan active).length) :
    (firstWindow initial rows J rewards start count hspan active)[k].input.state =
      (originalPrefix initial rows J rewards start count hspan active k hkcount).finalState := by
  have hlength := firstWindow_length_le_count initial rows J rewards start count hspan active
  have hklt : k < count := lt_of_lt_of_le hkwindow hlength
  rw [firstWindow_record_eq_actualRunRecordAt initial rows J rewards start count hspan
    active hfirst k hklt hkwindow]
  rfl

private theorem inputCoordinator_first_of_prepared_first
    (record : Record p rate)
    (outcome : CoordinatorRoundDispatch.FirstOutcome
      (ReferenceActivePhysicalStep.firstInput record.input))
    (hcut : record.output.preparation.coordinator = .first outcome) :
    record.input.state.coordinator = .first := by
  have hprepared : record.output.preparation =
      ReferenceActivePhysicalStep.prepare record.input := by
    rw [record.output_eq]
    rfl
  rw [hprepared] at hcut
  cases hstate : record.input.state.coordinator with
  | first => rfl
  | live registers owned base =>
      cases hdispatch : CoordinatorRoundDispatch.dispatch
          (.live (ReferenceActivePhysicalStep.liveInput record.input registers owned base)) with
      | live actualOutcome =>
          simp [ReferenceActivePhysicalStep.prepare, ReferenceActivePhysicalStep.dispatch,
            hstate, hdispatch] at hcut
          change ReferenceActivePhysicalStep.DispatchCut.live registers owned base actualOutcome =
            .first outcome at hcut
          cases hcut
  | collection payload ledger proposal =>
      by_cases hvalid : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
      · let cutoff : Fin p.T := ⟨ledger.cutoff - 1, by omega⟩
        let clock := ReferenceActivePhysicalStep.collectionClock payload ledger proposal cutoff
        cases hdispatch : CoordinatorRoundDispatch.dispatch
            (.collection (ReferenceActivePhysicalStep.collectionInput record.input payload ledger
              clock cutoff)) with
        | collection actualOutcome =>
            simp [ReferenceActivePhysicalStep.prepare, ReferenceActivePhysicalStep.dispatch,
              hstate, hvalid, cutoff, clock, hdispatch] at hcut
            change ReferenceActivePhysicalStep.DispatchCut.collection payload ledger clock cutoff
              actualOutcome = .first outcome at hcut
            cases hcut
      · simp [ReferenceActivePhysicalStep.prepare, ReferenceActivePhysicalStep.dispatch,
          hstate, hvalid] at hcut
  | dagger =>
      simp [ReferenceActivePhysicalStep.prepare, ReferenceActivePhysicalStep.dispatch,
        hstate] at hcut

private theorem inputCoordinator_live_of_prepared_live
    (record : Record p rate)
    (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
    (base : Fin (p.m - 1) → ℕ)
    (outcome : CoordinatorRoundDispatch.LiveOutcome
      (ReferenceActivePhysicalStep.liveInput record.input registers owned base))
    (hcut : record.output.preparation.coordinator =
      .live registers owned base outcome) :
    record.input.state.coordinator = .live registers owned base := by
  have hprepared : record.output.preparation =
      ReferenceActivePhysicalStep.prepare record.input := by
    rw [record.output_eq]
    rfl
  rw [hprepared] at hcut
  cases hstate : record.input.state.coordinator with
  | first =>
      cases hdispatch : CoordinatorRoundDispatch.dispatch
          (.first (ReferenceActivePhysicalStep.firstInput record.input)) with
      | first actualOutcome =>
          simp [ReferenceActivePhysicalStep.prepare, ReferenceActivePhysicalStep.dispatch,
            hstate, hdispatch] at hcut
          change ReferenceActivePhysicalStep.DispatchCut.first actualOutcome =
            .live registers owned base outcome at hcut
          cases hcut
  | live oldRegisters oldOwned oldBase =>
      cases hdispatch : CoordinatorRoundDispatch.dispatch
          (.live (ReferenceActivePhysicalStep.liveInput record.input oldRegisters oldOwned oldBase)) with
      | live actualOutcome =>
          simp [ReferenceActivePhysicalStep.prepare, ReferenceActivePhysicalStep.dispatch,
            hstate, hdispatch] at hcut
          change ReferenceActivePhysicalStep.DispatchCut.live oldRegisters oldOwned oldBase actualOutcome =
            .live registers owned base outcome at hcut
          cases hcut
          rfl
  | collection payload ledger proposal =>
      by_cases hvalid : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
      · let cutoff : Fin p.T := ⟨ledger.cutoff - 1, by omega⟩
        let clock := ReferenceActivePhysicalStep.collectionClock payload ledger proposal cutoff
        cases hdispatch : CoordinatorRoundDispatch.dispatch
            (.collection (ReferenceActivePhysicalStep.collectionInput record.input payload ledger
              clock cutoff)) with
        | collection actualOutcome =>
            simp [ReferenceActivePhysicalStep.prepare, ReferenceActivePhysicalStep.dispatch,
              hstate, hvalid, cutoff, clock, hdispatch] at hcut
            change ReferenceActivePhysicalStep.DispatchCut.collection payload ledger clock cutoff
              actualOutcome = .live registers owned base outcome at hcut
            cases hcut
      · simp [ReferenceActivePhysicalStep.prepare, ReferenceActivePhysicalStep.dispatch,
          hstate, hvalid] at hcut
  | dagger =>
      simp [ReferenceActivePhysicalStep.prepare, ReferenceActivePhysicalStep.dispatch,
        hstate] at hcut

/-- First-assignment complement mass along the original `H.run` prefix,
before the first actual chosen coordinator cutoff. -/
theorem run_first_complement_mass
    (initial : ReferenceActivePhysicalHorizon.State p rate) (rows : CompletePublicTable.CompleteRows p)
    (J : Fin (M p)) (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (active : allActiveAtStart initial start) (hfirst : initial.coordinator = .first) :
    ∀ k (hkcount : k ≤ count)
      (_hkwindow : k ≤ (firstWindow initial rows J rewards start count hspan active).length),
      let runPrefix := originalPrefix initial rows J rewards start count hspan active k hkcount
      match runPrefix.finalState.coordinator with
      | .first => k = 0
      | .collection _ _ _ => False
      | .dagger => True
      | .live r q base =>
          (∀ a, r.complementScores a + q.queue a ≤ k * D p) ∧
          (∀ a, q.previousService a ≤ D p) ∧
          (∀ i, base i = 0) ∧
          ∃ birth, birth ∈ (originalRun initial rows J rewards start count hspan active).records ∧
            ReferenceAssignmentPayloadPersistence.InstallationBirth birth r.payload ∧
            birth.input.time.val = start := by
  intro k hkcount _hkwindow
  let runPrefix := originalPrefix initial rows J rewards start count hspan active k hkcount
  have hInv := run_first_mass_prefix initial rows J rewards start count hspan active hfirst
    k hkcount _hkwindow
  cases hcoord : runPrefix.finalState.coordinator with
  | first =>
      simpa [firstMassInvariant, runPrefix, hcoord] using hInv
  | collection payload ledger savedProposal =>
      simp only [firstMassInvariant, runPrefix, hcoord] at hInv
  | dagger =>
      simp [runPrefix, hcoord]
  | live r q base =>
      simp only [runPrefix, hcoord]
      simp only [firstMassInvariant, runPrefix, hcoord] at hInv
      rcases hInv with ⟨hmass, hprevious, hbase, birth, hbirthMem, hbirth, hbirthTime⟩
      obtain ⟨suffix, hrecords⟩ := ReferenceCollectionPhaseHistory.run_records_prefix
        initial rows J rewards start k (count - k) (by omega) active
      have hrecords' :
          (originalRun initial rows J rewards start count hspan active).records =
            runPrefix.records ++ suffix := by
        simpa [originalRun, runPrefix, originalPrefix,
          Nat.add_sub_of_le hkcount] using hrecords
      refine ⟨hmass, hprevious, hbase, birth, ?_, hbirth, hbirthTime⟩
      rw [hrecords']
      exact List.mem_append_left _ hbirthMem

/-- At a literal first or continuing live tail in the actual first-live
window, the actual recorder output enters the same checked service pass. The
numeric premises are constructed from the original prefix theorem above. -/
theorem run_first_service_pass_budget
    (initial : ReferenceActivePhysicalHorizon.State p rate) (rows : CompletePublicTable.CompleteRows p)
    (J : Fin (M p)) (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (active : allActiveAtStart initial start) (hfirst : initial.coordinator = .first) :
    ∀ k : Fin (firstWindow initial rows J rewards start count hspan active).length,
      let record := (firstWindow initial rows J rewards start count hspan active)[k.val]
      match record.output.preparation.coordinator with
      | .first (.chosen installed _) =>
          ∀ recording,
            CoordinatorRecorderComplementBridge.run
              (ReferenceActivePhysicalStep.liveRecordingInput record.output.preparation
                installed.registers installed.startRoundResult) = some recording →
            ∃ serviced,
              CoordinatorLiveServiceFinish.servicePass installed.registers
                installed.ownedRegisters recording = .ok serviced ∧
              (∀ a, serviced.score a + serviced.queue a ≤ (k.val + 1) * D p) ∧
              (ReferenceActivePhysicalStep.livePostChoice record.output.preparation
                installed.registers installed.ownedRegisters installed.followerBaseScore
                installed.startRoundResult).recording = some recording
      | .live registers owned base (.continuingChosen dispatched _ _ _) =>
          let actualRegisters :=
            ReferenceActivePhysicalStep.liveRegistersAt registers record.input.time
          let actualOwned :=
            ReferenceActivePhysicalStep.liveOwnedAt registers owned record.input.time
          ∀ recording,
            CoordinatorRecorderComplementBridge.run
              (ReferenceActivePhysicalStep.liveRecordingInput record.output.preparation
                actualRegisters dispatched.startResult) = some recording →
            ∃ serviced,
              CoordinatorLiveServiceFinish.servicePass actualRegisters actualOwned recording =
                .ok serviced ∧
              (∀ a, serviced.score a + serviced.queue a ≤ (k.val + 1) * D p) ∧
              (ReferenceActivePhysicalStep.livePostChoice record.output.preparation
                actualRegisters actualOwned base dispatched.startResult).recording = some recording
      | _ => True := by
  intro k
  dsimp only
  let record := (firstWindow initial rows J rewards start count hspan active)[k.val]
  have hlength := firstWindow_length_le_count initial rows J rewards start count hspan active
  have hkcount : k.val ≤ count := le_trans k.isLt.le hlength
  have hinputState := firstWindow_input_state_eq_prefix initial rows J rewards start count
    hspan active hfirst k.val hkcount k.isLt
  have hInv := run_first_mass_prefix initial rows J rewards start count hspan active hfirst
    k.val hkcount k.isLt.le
  cases hcut : record.output.preparation.coordinator with
  | first outcome =>
      cases outcome with
      | choiceDomainFailure installed => trivial
      | recorderBoundaryFailure installed => trivial
      | choiceRejected installed => trivial
      | chosen installed selection =>
          intro recording hrecorded
          have hinputFirst := inputCoordinator_first_of_prepared_first record
            (.chosen installed selection) hcut
          have hprefixFirst :
              (originalPrefix initial rows J rewards start count hspan active k.val hkcount).finalState.coordinator =
                .first := by
            have hcoord := congrArg (fun state : ReferenceActivePhysicalHorizon.State p rate => state.coordinator) hinputState
            exact hcoord.symm.trans hinputFirst
          simp only [firstMassInvariant, hprefixFirst] at hInv
          have hchosen : CoordinatorRoundDispatch.dispatchFirst
              (ReferenceActivePhysicalStep.firstInput record.input) =
                .chosen installed selection := by
            have hprepared : record.output.preparation =
                ReferenceActivePhysicalStep.prepare record.input := by
              rw [record.output_eq]
              rfl
            rw [hprepared] at hcut
            simpa [ReferenceActivePhysicalStep.prepare,
              ReferenceActivePhysicalStep.dispatch_first, hinputFirst] using hcut
          have hseed := ReferenceActivePhysicalStep.dispatchFirst_zero_seed
            record.input installed selection hchosen
          rcases hseed with ⟨hscore0, hqueue0, hprevious0, _⟩
          have hpreviousBound :
              ∀ a, installed.ownedRegisters.previousService a ≤ D p := by
            intro a
            rw [hprevious0 a]
            exact Nat.zero_le _
          have hmass : ∀ a, installed.registers.complementScores a +
              installed.ownedRegisters.queue a ≤ k.val * D p := by
            intro a
            rw [hscore0 a, hqueue0 a, hInv]
            simp
          have hkT : k.val + 1 ≤ p.T := by omega
          obtain ⟨serviced, hpass, hmassNext, _⟩ :=
            servicePass_of_prefix_mass installed.registers installed.ownedRegisters
              recording k.val hmass hpreviousBound hkT
          have hrecordingRetained :=
            ReferenceCoordinatorLiveRecording.livePostChoice_recording_eq_run
              record.output.preparation installed.registers installed.ownedRegisters
              installed.followerBaseScore installed.startRoundResult
          refine ⟨serviced, hpass, hmassNext, ?_⟩
          exact hrecordingRetained.trans hrecorded

  | live registers owned base outcome =>
      cases outcome with
      | clockFailure failure hfailure => trivial
      | initializerFailure dispatched hstart checked hchecked => trivial
      | localFailure dispatched hstart reason => trivial
      | cutoffChosen dispatched hstart ledger hinit ledgerCandidate hvalid hclock hpending
          hassignment selection => trivial
      | continuingChosen dispatched hstart continuation selection =>
          intro recording hrecorded
          have hinputLive := inputCoordinator_live_of_prepared_live record registers owned base
            (.continuingChosen dispatched hstart continuation selection) hcut
          have hprefixLive :
              (originalPrefix initial rows J rewards start count hspan active k.val hkcount).finalState.coordinator =
                .live registers owned base := by
            have hcoord := congrArg (fun state : ReferenceActivePhysicalHorizon.State p rate => state.coordinator) hinputState
            exact hcoord.symm.trans hinputLive
          simp only [firstMassInvariant, hprefixLive] at hInv
          rcases hInv with ⟨hmassOld, hpreviousOld, _, _, _, _, _⟩
          let actualRegisters := ReferenceActivePhysicalStep.liveRegistersAt registers record.input.time
          let actualOwned := ReferenceActivePhysicalStep.liveOwnedAt registers owned record.input.time
          have hmass : ∀ a, actualRegisters.complementScores a + actualOwned.queue a ≤
              k.val * D p := by
            intro a
            simpa [actualRegisters, actualOwned,
              ReferenceActivePhysicalStep.liveRegistersAt,
              ReferenceActivePhysicalStep.liveOwnedAt] using hmassOld a
          have hprevious : ∀ a, actualOwned.previousService a ≤ D p := by
            intro a
            simpa [actualRegisters, actualOwned,
              ReferenceActivePhysicalStep.liveRegistersAt,
              ReferenceActivePhysicalStep.liveOwnedAt] using hpreviousOld a
          have hkT : k.val + 1 ≤ p.T := by omega
          obtain ⟨serviced, hpass, hmassNext, _⟩ :=
            servicePass_of_prefix_mass actualRegisters actualOwned recording k.val
              hmass hprevious hkT
          have hrecordingRetained :=
            ReferenceCoordinatorLiveRecording.livePostChoice_recording_eq_run
              record.output.preparation actualRegisters actualOwned base dispatched.startResult
          refine ⟨serviced, hpass, hmassNext, ?_⟩
          exact hrecordingRetained.trans hrecorded
  | collection payload ledger clock cutoff outcome => trivial
  | invalidCollectionCutoff => trivial
  | dagger => trivial

private theorem livePostChoice_domain_failures_excluded
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (hbudget : ∀ recording,
      CoordinatorRecorderComplementBridge.run
        (ReferenceActivePhysicalStep.liveRecordingInput prepared r started) = some recording →
      ∃ serviced, CoordinatorLiveServiceFinish.servicePass r q recording = .ok serviced) :
    (ReferenceActivePhysicalStep.livePostChoice prepared r q base started).failure ≠
        some (.live .queueInputDomainFailure) ∧
      (ReferenceActivePhysicalStep.livePostChoice prepared r q base started).failure ≠
        some (.live .previousServiceInputDomainFailure) ∧
      (ReferenceActivePhysicalStep.livePostChoice prepared r q base started).failure ≠
        some (.live .arrivalOutputDomainFailure) ∧
      (ReferenceActivePhysicalStep.livePostChoice prepared r q base started).failure ≠
        some (.live .serviceOutputDomainFailure) ∧
      (ReferenceActivePhysicalStep.livePostChoice prepared r q base started).failure ≠
        some (.live .scoreOutputDomainFailure) ∧
      (ReferenceActivePhysicalStep.livePostChoice prepared r q base started).failure ≠
        some (.live .queueOutputDomainFailure) := by
  classical
  unfold ReferenceActivePhysicalStep.livePostChoice
  cases hrecorded : CoordinatorRecorderComplementBridge.run
      (ReferenceActivePhysicalStep.liveRecordingInput prepared r started) with
  | none =>
      simp [ReferenceActivePhysicalStep.coordinatorFailure]
  | some recording =>
      obtain ⟨serviced, hservice⟩ := hbudget recording hrecorded
      simp only [hservice]
      cases hconfirmation : CoordinatorLocalArmChoice.confirmationUpdate r.payload
          started.pending (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
          x.time x.row prepared.coordinatorObservation with
      | none =>
          simp [ReferenceActivePhysicalStep.coordinatorFailure]
      | some pending =>
          cases hfinish : CoordinatorPhaseClock.finishRound p rate.eta.val x.time
              started.clock pending x.row with
          | error failure =>
              cases failure <;>
                simp [hfinish, ReferenceActivePhysicalStep.coordinatorFailure,
                  CoordinatorLiveServiceFinish.finishFailureCode]
          | ok finished =>
              simp [hfinish]
/-- Exactly the six LIVE-tail service-domain failures are ruled out on actual
first-live records. Dispatch, recorder, confirmation, finish-clock, collection,
and absorbing-dagger outcomes retain their separate original tags. -/
theorem run_first_service_domain_failures_excluded
    (initial : ReferenceActivePhysicalHorizon.State p rate) (rows : CompletePublicTable.CompleteRows p)
    (J : Fin (M p)) (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (active : allActiveAtStart initial start) (hfirst : initial.coordinator = .first) :
    ∀ k : Fin (firstWindow initial rows J rewards start count hspan active).length,
      let record := (firstWindow initial rows J rewards start count hspan active)[k.val]
      match record.output.preparation.coordinator with
      | .first (.chosen _ _) =>
          record.output.coordinator.failure ≠ some (.live .queueInputDomainFailure) ∧
          record.output.coordinator.failure ≠ some (.live .previousServiceInputDomainFailure) ∧
          record.output.coordinator.failure ≠ some (.live .arrivalOutputDomainFailure) ∧
          record.output.coordinator.failure ≠ some (.live .serviceOutputDomainFailure) ∧
          record.output.coordinator.failure ≠ some (.live .scoreOutputDomainFailure) ∧
          record.output.coordinator.failure ≠ some (.live .queueOutputDomainFailure)
      | .live _ _ _ (.continuingChosen _ _ _ _) =>
          record.output.coordinator.failure ≠ some (.live .queueInputDomainFailure) ∧
          record.output.coordinator.failure ≠ some (.live .previousServiceInputDomainFailure) ∧
          record.output.coordinator.failure ≠ some (.live .arrivalOutputDomainFailure) ∧
          record.output.coordinator.failure ≠ some (.live .serviceOutputDomainFailure) ∧
          record.output.coordinator.failure ≠ some (.live .scoreOutputDomainFailure) ∧
          record.output.coordinator.failure ≠ some (.live .queueOutputDomainFailure)
      | _ => True := by
  intro k
  dsimp only
  let record := (firstWindow initial rows J rewards start count hspan active)[k.val]
  cases hcut : record.output.preparation.coordinator with
  | first outcome =>
      cases outcome with
      | choiceDomainFailure installed => trivial
      | recorderBoundaryFailure installed => trivial
      | choiceRejected installed => trivial
      | chosen installed selection =>
          have hbudgetFull := run_first_service_pass_budget initial rows J rewards start count
            hspan active hfirst k
          simp only [record, hcut] at hbudgetFull
          have hbudget : ∀ recording,
              CoordinatorRecorderComplementBridge.run
                (ReferenceActivePhysicalStep.liveRecordingInput record.output.preparation
                  installed.registers installed.startRoundResult) = some recording →
              ∃ serviced, CoordinatorLiveServiceFinish.servicePass installed.registers
                installed.ownedRegisters recording = .ok serviced := by
            intro recording hrecorded
            obtain ⟨serviced, hservice, _, _⟩ := hbudgetFull recording hrecorded
            exact ⟨serviced, hservice⟩
          have houtput : record.output.coordinator =
              record.output.preparation.observeCoordinator := by
            rw [record.output_eq]
            rfl
          have hobs := ReferenceActivePhysicalStep.observeCoordinator_first_equation
            record.output.preparation (.chosen installed selection) hcut
          by_cases hselector :
              (ReferenceActivePhysicalStep.DispatchCut.first
                (.chosen installed selection : CoordinatorRoundDispatch.FirstOutcome
                  (ReferenceActivePhysicalStep.firstInput record.input))).selection = none
          · rw [houtput, hobs]
            simp [hselector, ReferenceActivePhysicalStep.coordinatorFailure]
          · rw [houtput, hobs]
            simpa [hselector] using livePostChoice_domain_failures_excluded
              record.input record.output.preparation installed.registers
              installed.ownedRegisters installed.followerBaseScore installed.startRoundResult
              hbudget
  | live registers owned base outcome =>
      cases outcome with
      | clockFailure failure hfailure => trivial
      | initializerFailure dispatched hstart checked hchecked => trivial
      | localFailure dispatched hstart reason => trivial
      | cutoffChosen dispatched hstart ledger hinit ledgerCandidate hvalid hclock hpending
          hassignment selection => trivial
      | continuingChosen dispatched hstart continuation selection =>
          let actualRegisters :=
            ReferenceActivePhysicalStep.liveRegistersAt registers record.input.time
          let actualOwned :=
            ReferenceActivePhysicalStep.liveOwnedAt registers owned record.input.time
          have hbudgetFull := run_first_service_pass_budget initial rows J rewards start count
            hspan active hfirst k
          simp only [record, hcut] at hbudgetFull
          have hbudget : ∀ recording,
              CoordinatorRecorderComplementBridge.run
                (ReferenceActivePhysicalStep.liveRecordingInput record.output.preparation
                  actualRegisters dispatched.startResult) = some recording →
              ∃ serviced, CoordinatorLiveServiceFinish.servicePass actualRegisters
                actualOwned recording = .ok serviced := by
            intro recording hrecorded
            obtain ⟨serviced, hservice, _, _⟩ := hbudgetFull recording hrecorded
            exact ⟨serviced, hservice⟩
          have houtput : record.output.coordinator =
              record.output.preparation.observeCoordinator := by
            rw [record.output_eq]
            rfl
          have hobs := ReferenceActivePhysicalStep.observeCoordinator_live_equation
            record.output.preparation registers owned base
            (.continuingChosen dispatched hstart continuation selection) hcut
          by_cases hselector :
              (ReferenceActivePhysicalStep.DispatchCut.live registers owned base
                (.continuingChosen dispatched hstart continuation selection)).selection = none
          · rw [houtput, hobs]
            simp [hselector, ReferenceActivePhysicalStep.coordinatorFailure]
          · rw [houtput, hobs]
            simpa [hselector, actualRegisters, actualOwned] using
              livePostChoice_domain_failures_excluded record.input
                record.output.preparation actualRegisters actualOwned base dispatched.startResult
                hbudget
  | collection payload ledger proposal => trivial
  | invalidCollectionCutoff => trivial
  | dagger => trivial

end Bandits.Support.ReferenceFirstComplementMassBudget
end
