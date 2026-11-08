/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceRunClockPreservation
public import Bandits.Support.ReferenceCoordinatorLiveRecording
public import Bandits.Support.ReferenceAssignmentPayloadChronology
public import Bandits.Support.ReferenceFirstLiveConfirmationHistory
public import Bandits.Support.ReferenceCollectionRawBufferHistory
public import Bandits.Support.CollectionRecordedScoreRecovery

import Lean.Elab.Tactic.Omega
import Mathlib.Data.List.TakeWhile
import Mathlib.Data.List.DropRight

/-!
# First-complement diagnostic queue replay

Sources: `sources/zip4/manuscript/appendix_a_local_protocol.tex:28-53`,
`sources/zip4/manuscript/06_interruptions.tex:9-70,246-269,294`,
`sources/zip4/manuscript/05_binary_transport.tex:354-396`, and
`sources/zip4/manuscript/04_slow_fast_learner.tex:157-165`.

The records below project the actual first-live physical run. Their queue
updates use the original checked coordinator service result and its retained
diagnostic, including failed and dagger records in the physical prefix. These
are zero-seeded diagnostic replays before the first chosen cutoff. They are not
the common full-horizon `RecordedQueueRun`, and do not establish recorder
truth, accepted-UP history, or a manuscript conclusion.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.CoordinatorRoundDispatch
open Bandits.Support.CoordinatorLiveChoiceRecorderStep
open Bandits.Support.CoordinatorLiveServiceFinish
open Bandits.Support.CoordinatorStartRoundCutoffDispatch
open Bandits.Support.CoordinatorCollectionLedger
open Bandits.Support.CoordinatorRecorderComplementBridge
open Bandits.Support.CanonicalFastSampling
open Bandits.Support.ReferenceAssignmentPayloadChronology
open Bandits.Support.ReferenceFirstLiveConfirmationHistory

namespace Bandits.Support.ReferenceFirstComplementReplay

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev State := ReferenceActivePhysicalHorizon.State
abbrev RoundRecord (p : Parameters) (rate : RateInput p) :=
  ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)

variable {p : Parameters} {rate : RateInput p}

/-- The literal queue input obtained by projecting one actual diagnostic.
The first coordinate is the source's live-before-grid service switch; the
second retains an arm-specific zero arrival when the diagnostic gate names
that arm. -/
def liveDiagnosticQueueRecord
    (payload : AssignmentStartPayload.Input p rate.eta)
    (arm : Fin p.K)
    (record : RoundRecord p rate) : Bool × ℕ :=
  (decide (record.input.time.val + 1 <
      FollowerCutoffScan.gridBoundary p rate.eta.val payload.sigma),
    CoordinatorCollectionLedger.localArrival
      (ReferenceCollectionRawBufferHistory.rawDiagnostic record) arm)

/-- The chronological diagnostic queue records on a retained prefix of the
same original first-live window. -/
def liveDiagnosticQueueRecords
    (payload : AssignmentStartPayload.Input p rate.eta)
    (arm : Fin p.K)
    (window : List (RoundRecord p rate)) (count : ℕ) : List (Bool × ℕ) :=
  (window.take count).map (liveDiagnosticQueueRecord payload arm)

private theorem replayLastService_append_one
    (capacity : ℕ) (initial : ℕ × ℕ) (retained : ℕ)
    (records : List (Bool × ℕ)) (record : Bool × ℕ) :
    CollectionKnownQueueContinuation.replayLastService capacity initial retained
        (records ++ [record]) =
      RecordedQueueRun.recordService capacity
        (QueueReplay.replay capacity initial records) record := by
  have hlast : (records ++ [record]).getLast? = some record :=
    List.getLast?_append_of_ne_nil records (by simp)
  simp only [CollectionKnownQueueContinuation.replayLastService,
    hlast, List.dropLast_concat]
  rw [RecordedQueueRun.transition_score_eq_add_recordService]
  exact Nat.add_sub_cancel_left _ _

private def originalRun
    (initial : State p rate) (rows : CompletePublicTable.CompleteRows p)
    (J : Fin (M p)) (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (active : allActiveAtStart initial start) :=
  ReferenceActivePhysicalHorizon.run initial rows J rewards start count hspan active

private def firstWindow
    (initial : State p rate) (rows : CompletePublicTable.CompleteRows p)
    (J : Fin (M p)) (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (active : allActiveAtStart initial start) :=
  ReferenceFirstLiveConfirmationHistory.firstLiveWindow
    (originalRun initial rows J rewards start count hspan active).records

private def originalPrefix
    (initial : State p rate) (rows : CompletePublicTable.CompleteRows p)
    (J : Fin (M p)) (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (active : allActiveAtStart initial start) (k : ℕ) (hk : k ≤ count) :=
  ReferenceActivePhysicalHorizon.run initial rows J rewards start k (by omega) active

private def replayInvariant (rows : CompletePublicTable.CompleteRows p)
    (J : Fin (M p)) (start k : ℕ) (window : List (RoundRecord p rate))
    (records : List (RoundRecord p rate)) (state : State p rate) : Prop :=
  match state.coordinator with
  | .first => k = 0
  | .collection _ _ _ => False
  | .dagger => True
  | .live r q base =>
      (∀ i, base i = 0) ∧
      (∃ birth, birth ∈ records ∧
        ReferenceAssignmentPayloadPersistence.InstallationBirth birth r.payload ∧
        birth.input.time.val = start ∧
        (∃ installed selection,
          birth.output.preparation.coordinator = .first (.chosen installed selection))) ∧
      (∀ i : Fin p.T, start ≤ i.val → i.val + 1 < start + k →
        FollowerCutoffScan.completeRowProposalBit p rate.eta.val (rows J) i = false) ∧
      (∀ a : FastArm r.payload.slowSet, ∀ record ∈ window.take k,
        (liveDiagnosticQueueRecord r.payload a.1 record).1 = true) ∧
      ∀ a : FastArm r.payload.slowSet,
        (r.complementScores a, q.queue a) =
          QueueReplay.replay (4 * r.payload.n) (0, 0)
            (liveDiagnosticQueueRecords r.payload a.1 window k) ∧
        q.previousService a =
          CollectionKnownQueueContinuation.replayLastService
            (4 * r.payload.n) (0, 0) 0
              (liveDiagnosticQueueRecords r.payload a.1 window k)

private theorem liveDiagnosticRecords_enabled_take_succ
    (payload : AssignmentStartPayload.Input p rate.eta)
    (arm : FastArm payload.slowSet)
    (window : List (RoundRecord p rate)) (k : ℕ)
    (hindex : k < window.length)
    (hprevious : ∀ record ∈ window.take k,
      (liveDiagnosticQueueRecord payload arm.1 record).1 = true)
    (henabled : (liveDiagnosticQueueRecord payload arm.1 window[k]).1 = true) :
    ∀ record ∈ window.take (k + 1),
      (liveDiagnosticQueueRecord payload arm.1 record).1 = true := by
  intro record hrecord
  rw [(List.take_append_getElem hindex).symm] at hrecord
  rcases List.mem_append.mp hrecord with hpreviousRecord | hcurrent
  · exact hprevious record hpreviousRecord
  · simp only [List.mem_singleton] at hcurrent
    subst record
    exact henabled

private theorem actualStepRecord_eq (record : RoundRecord p rate) :
    ReferenceAssignmentPayloadChronology.actualStepRecord record.input = record := by
  cases record with
  | mk input output houtput =>
      cases houtput
      rfl

/-- A retained first-live element is the same computed record as the
successor constructor of the original run. The full public rows, selected
index, and rewards remain those of the original call. -/
private theorem firstWindow_record_eq_actualRunRecordAt
    (initial : State p rate) (rows : CompletePublicTable.CompleteRows p)
    (J : Fin (M p)) (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (active : allActiveAtStart initial start)
    (hfirst : initial.coordinator = .first)
    (k : ℕ) (hkcount : k < count)
    (hkwindow : k < (firstWindow initial rows J rewards start count hspan active).length) :
    (firstWindow initial rows J rewards start count hspan active)[k] =
      ReferenceAssignmentPayloadChronology.actualRunRecordAt initial rows J rewards
        start k (by omega) active := by
  let E := originalRun initial rows J rewards start count hspan active
  let W := firstWindow initial rows J rewards start count hspan active
  have hseed : ReferenceCoordinatorClockDomains.clockAt rows J start initial := by
    simp [ReferenceCoordinatorClockDomains.clockAt, hfirst]
  have hclock := ReferenceRunClockPreservation.run_clockAt initial rows J rewards
    start count hspan active hseed
  have hwindowPrefix : W.IsPrefix E.records := by
    exact List.takeWhile_prefix _
  have hkE : k < E.records.length := lt_of_lt_of_le hkwindow hwindowPrefix.length_le
  have hwindowElem : W[k] = E.records[k] := hwindowPrefix.getElem hkwindow
  have htimeMap := hclock.2.2.1
  have hkMap : k < (E.records.map fun record => record.input.time.val).length := by
    simpa using hkE
  have htimeElem :
      (E.records.map fun record => record.input.time.val)[k] = W[k].input.time.val := by
    calc
      (E.records.map fun record => record.input.time.val)[k] = E.records[k].input.time.val := by
        simp
      _ = W[k].input.time.val := by rw [← hwindowElem]
  have hwindowTime : W[k].input.time.val = start + k := by
    have htimeMap' :
        E.records.map (fun record => record.input.time.val) =
          ReferenceActivePhysicalHorizon.calendar start count := by
      simpa [E, originalRun] using htimeMap
    have hkcalendar : k < (ReferenceActivePhysicalHorizon.calendar start count).length := by
      simpa [ReferenceActivePhysicalHorizon.calendar] using hkcount
    have hcalendar : (ReferenceActivePhysicalHorizon.calendar start count)[k] = start + k := by
      simp [ReferenceActivePhysicalHorizon.calendar]
    calc
      W[k].input.time.val = (E.records.map fun record => record.input.time.val)[k] := htimeElem.symm
      _ = (ReferenceActivePhysicalHorizon.calendar start count)[k] := by
        exact List.getElem_of_eq htimeMap' hkMap
      _ = start + k := hcalendar
  let next := originalPrefix initial rows J rewards start count hspan active (k + 1) (by omega)
  let actual := ReferenceAssignmentPayloadChronology.actualRunRecordAt initial rows J rewards
    start k (by omega) active
  have hnextPrefix : ∃ suffix, E.records = next.records ++ suffix := by
    obtain ⟨suffix, hrecords⟩ := ReferenceCollectionPhaseHistory.run_records_prefix
      initial rows J rewards start (k + 1) (count - (k + 1)) (by omega) active
    refine ⟨suffix, ?_⟩
    simpa [E, next, originalRun, originalPrefix, Nat.add_sub_of_le (show k + 1 ≤ count by omega)]
      using hrecords
  obtain ⟨suffix, hrecords⟩ := hnextPrefix
  have hsuccessor := ReferenceAssignmentPayloadChronology.run_successor_actualRunRecordAt
    initial rows J rewards start k (by omega) active
  have hactualMemNext : actual ∈ next.records := by
    change actual ∈
      (ReferenceActivePhysicalHorizon.run initial rows J rewards start (k + 1)
        (by omega) active).records
    rw [hsuccessor]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  have hactualMemE : actual ∈ E.records := by
    rw [hrecords]
    exact List.mem_append_left _ hactualMemNext
  have hwindowMemE : W[k] ∈ E.records := by
    rw [hwindowElem]
    exact List.getElem_mem hkE
  have hactualTime : actual.input.time.val = start + k := rfl
  exact ReferenceAssignmentPayloadChronology.run_records_time_injective
    initial rows J rewards start count hspan active hwindowMemE hactualMemE
    (hwindowTime.trans hactualTime.symm)

private theorem firstWindow_length_le_count
    (initial : State p rate) (rows : CompletePublicTable.CompleteRows p)
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
    (initial : State p rate) (rows : CompletePublicTable.CompleteRows p)
    (J : Fin (M p)) (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (active : allActiveAtStart initial start)
    (hfirst : initial.coordinator = .first)
    (k : ℕ) (hkcount : k ≤ count)
    (hkwindow : k < (firstWindow initial rows J rewards start count hspan active).length) :
    (firstWindow initial rows J rewards start count hspan active)[k].input.state =
      (originalPrefix initial rows J rewards start count hspan active k hkcount).finalState := by
  have hlength := firstWindow_length_le_count initial rows J rewards start count hspan active
  rw [firstWindow_record_eq_actualRunRecordAt initial rows J rewards start count hspan
    active hfirst k (lt_of_lt_of_le hkwindow hlength) hkwindow]
  rfl

private theorem preparedFirst_noSelection_dagger
    (record : RoundRecord p rate)
    (outcome : CoordinatorRoundDispatch.FirstOutcome
      (ReferenceActivePhysicalStep.firstInput record.input))
    (hcut : record.output.preparation.coordinator = .first outcome)
    (hselection : (ReferenceActivePhysicalStep.DispatchCut.first outcome).selection = none) :
    record.output.next.coordinator = .dagger := by
  have hprepared : record.output.preparation = ReferenceActivePhysicalStep.prepare record.input := by
    rw [record.output_eq]
    rfl
  have hobs := ReferenceActivePhysicalStep.observeCoordinator_first_equation
    record.output.preparation outcome hcut
  have hconfiguration :
      record.output.preparation.observeCoordinator.configuration = .dagger := by
    rw [hobs]
    simp [hselection, ReferenceActivePhysicalStep.coordinatorFailure]
  rw [record.output_eq]
  exact (ReferenceActivePhysicalStep.step_next_fields record.input).1.trans
    (by simpa only [hprepared] using hconfiguration)

private theorem live_clock_boundary_eq
    (rows : CompletePublicTable.CompleteRows p) (J : Fin (M p))
    (time : ℕ) (state : State p rate)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ)
    (hstate : state.coordinator = .live r q base)
    (hclock : ReferenceCoordinatorClockDomains.clockAt rows J time state) :
    r.gridBoundary = FollowerCutoffScan.gridBoundary p rate.eta.val r.payload.sigma := by
  simp only [ReferenceCoordinatorClockDomains.clockAt, hstate] at hclock
  rcases hclock with ⟨_, hvalid, hsigma, _, hgrid, _, _, _⟩
  calc
    r.gridBoundary = r.priorClock.g := hgrid
    _ = CoordinatorPhaseClock.boundaryFromSigma p rate.eta.val r.priorClock.sigma := hvalid.1
    _ = CoordinatorPhaseClock.boundaryFromSigma p rate.eta.val (some r.payload.sigma) :=
      congrArg (CoordinatorPhaseClock.boundaryFromSigma p rate.eta.val) hsigma
    _ = FollowerCutoffScan.gridBoundary p rate.eta.val r.payload.sigma := rfl

private theorem servicePass_ok_recording_eq
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (recording : CoordinatorRecordingOperation.Output p)
    (serviced : CoordinatorLiveServiceFinish.ServicedRegisters r q)
    (h : CoordinatorLiveServiceFinish.servicePass r q recording = .ok serviced) :
    serviced.recording = recording := by
  have hmap :
      (CoordinatorLiveServiceFinish.servicePass r q recording).map
          (fun result => result.recording) =
        (CoordinatorLiveServiceFinish.servicePass r q recording).map
          (fun _ => recording) := by
    classical
    unfold CoordinatorLiveServiceFinish.servicePass
    dsimp only
    split_ifs <;> simp [Except.map]
  have hmapped := congrArg
    (fun result : Except CoordinatorLiveServiceFinish.Failure
      (CoordinatorLiveServiceFinish.ServicedRegisters r q) =>
        result.map (fun output => output.recording)) h
  rw [hmap, h] at hmapped
  exact (Except.ok.inj hmapped).symm

private def postChoiceRegisters
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    {q : CoordinatorLiveServiceFinish.OwnedRegisters r}
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (finished : CoordinatorPhaseClock.FinishRoundResult p)
    (serviced : CoordinatorLiveServiceFinish.ServicedRegisters r q) :
    CoordinatorLiveChoiceRecorderStep.Registers p rate.eta :=
  { payload := r.payload
    priorClock := finished.clock
    pendingAtChoice := finished.pending
    time := x.time
    gridBoundary := finished.clock.g
    complementScores := serviced.score }

private def postChoiceOwned
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    {q : CoordinatorLiveServiceFinish.OwnedRegisters r}
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (finished : CoordinatorPhaseClock.FinishRoundResult p)
    (serviced : CoordinatorLiveServiceFinish.ServicedRegisters r q) :
    CoordinatorLiveServiceFinish.OwnedRegisters
      (postChoiceRegisters r x finished serviced) :=
  { queue := serviced.queue
    previousService := serviced.previousService }

private theorem livePostChoice_success_or_dagger
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ)
    (started : CoordinatorPhaseClock.StartRoundResult p) :
    (ReferenceActivePhysicalStep.livePostChoice prepared r q base started).configuration = .dagger ∨
      ∃ recording serviced pending finished,
        CoordinatorRecorderComplementBridge.run
          (ReferenceActivePhysicalStep.liveRecordingInput prepared r started) = some recording ∧
        CoordinatorLiveServiceFinish.servicePass r q recording = .ok serviced ∧
        serviced.recording = recording ∧
        CoordinatorLocalArmChoice.confirmationUpdate r.payload started.pending
          (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
          x.time x.row prepared.coordinatorObservation = some pending ∧
        CoordinatorPhaseClock.finishRound p rate.eta.val x.time started.clock pending x.row =
          .ok finished ∧
        (ReferenceActivePhysicalStep.livePostChoice prepared r q base started).configuration =
          .live (postChoiceRegisters r x finished serviced)
            (postChoiceOwned r x finished serviced) base := by
  classical
  unfold ReferenceActivePhysicalStep.livePostChoice
  cases hrecording : CoordinatorRecorderComplementBridge.run
      (ReferenceActivePhysicalStep.liveRecordingInput prepared r started) with
  | none =>
      simp [ReferenceActivePhysicalStep.coordinatorFailure]
  | some recording =>
      cases hservice : CoordinatorLiveServiceFinish.servicePass r q recording with
      | error failure =>
          simp [hservice, ReferenceActivePhysicalStep.coordinatorFailure]
      | ok serviced =>
          cases hconfirmation : CoordinatorLocalArmChoice.confirmationUpdate r.payload
              started.pending (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
              x.time x.row prepared.coordinatorObservation with
          | none =>
              simp [hservice,
                ReferenceActivePhysicalStep.coordinatorFailure]
          | some pending =>
              cases hfinish : CoordinatorPhaseClock.finishRound p rate.eta.val x.time
                  started.clock pending x.row with
              | error failure =>
                  simp [hservice, hfinish,
                    ReferenceActivePhysicalStep.coordinatorFailure]
              | ok finished =>
                  apply Or.inr
                  refine ⟨recording, serviced, pending, finished, rfl, hservice,
                    servicePass_ok_recording_eq r q recording serviced hservice,
                    rfl, hfinish, ?_⟩
                  simp [hservice, hfinish, postChoiceRegisters, postChoiceOwned]

private theorem livePostChoice_actual_recording
    (record : RoundRecord p rate)
    (prepared : ReferenceActivePhysicalStep.PreparedRound record.input)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (hprepared : record.output.preparation = prepared)
    (htail : prepared.observeCoordinator =
      ReferenceActivePhysicalStep.livePostChoice prepared r q base started)
    (recording : CoordinatorRecordingOperation.Output p)
    (hrecording : CoordinatorRecorderComplementBridge.run
      (ReferenceActivePhysicalStep.liveRecordingInput prepared r started) = some recording) :
    record.output.coordinator.recording = some recording := by
  have hretained := ReferenceCoordinatorLiveRecording.livePostChoice_recording_eq_run
    prepared r q base started
  calc
    record.output.coordinator.recording = prepared.observeCoordinator.recording := by
      rw [record.output_eq]
      change (ReferenceActivePhysicalStep.prepare record.input).observeCoordinator.recording =
        prepared.observeCoordinator.recording
      have hprepEq : ReferenceActivePhysicalStep.prepare record.input = prepared := by
        calc
          ReferenceActivePhysicalStep.prepare record.input =
              (ReferenceActivePhysicalStep.step record.input).preparation := rfl
          _ = record.output.preparation := by rw [record.output_eq]
          _ = prepared := hprepared
      exact congrArg (fun prep : ReferenceActivePhysicalStep.PreparedRound record.input =>
        prep.observeCoordinator.recording) hprepEq
    _ = (ReferenceActivePhysicalStep.livePostChoice prepared r q base started).recording :=
      congrArg CoordinatorObservation.recording htail
    _ = some recording := by rw [hretained, hrecording]

private theorem diagnostic_arrival_eq
    (record : RoundRecord p rate)
    (payload : AssignmentStartPayload.Input p rate.eta)
    (recording : CoordinatorRecordingOperation.Output p)
    (hrecording : record.output.coordinator.recording = some recording)
    (arm : FastArm payload.slowSet) :
    CoordinatorCollectionLedger.localArrival
        (ReferenceCollectionRawBufferHistory.rawDiagnostic record) arm.1 =
      CoordinatorLiveServiceFinish.complementArrival payload recording arm := by
  cases hgate : recording.gateArm with
  | none =>
      simp [ReferenceCollectionRawBufferHistory.rawDiagnostic, hrecording, hgate,
        CoordinatorCollectionLedger.localArrival,
        CoordinatorLiveServiceFinish.complementArrival]
  | some gate =>
      simp [ReferenceCollectionRawBufferHistory.rawDiagnostic, hrecording, hgate,
        CoordinatorCollectionLedger.localArrival,
        CoordinatorLiveServiceFinish.complementArrival]

private theorem diagnostic_serviced_extension
    (window : List (RoundRecord p rate)) (count : ℕ)
    (record : RoundRecord p rate)
    (hindex : count < window.length)
    (hrecord : record = window[count])
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (serviced : CoordinatorLiveServiceFinish.ServicedRegisters r q)
    (arm : FastArm r.payload.slowSet)
    (nextScore nextQueue nextPrevious : FastArm r.payload.slowSet → ℕ)
    (hstate : (r.complementScores arm, q.queue arm) =
      QueueReplay.replay (4 * r.payload.n) (0, 0)
        (liveDiagnosticQueueRecords r.payload arm.1 window count))
    (hnextScore : nextScore arm = serviced.score arm)
    (hnextQueue : nextQueue arm = serviced.queue arm)
    (hnextPrevious : nextPrevious arm = serviced.previousService arm)
    (hrecording : record.output.coordinator.recording = some serviced.recording)
    (henabled : decide (record.input.time.val + 1 <
      FollowerCutoffScan.gridBoundary p rate.eta.val r.payload.sigma) = true) :
    (nextScore arm, nextQueue arm) =
      QueueReplay.replay (4 * r.payload.n) (0, 0)
        (liveDiagnosticQueueRecords r.payload arm.1 window (count + 1)) ∧
    nextPrevious arm =
      CollectionKnownQueueContinuation.replayLastService (4 * r.payload.n) (0, 0) 0
        (liveDiagnosticQueueRecords r.payload arm.1 window (count + 1)) := by
  have hraw := diagnostic_arrival_eq record r.payload serviced.recording hrecording arm
  have harrival : serviced.arrival arm =
      CoordinatorCollectionLedger.localArrival
        (ReferenceCollectionRawBufferHistory.rawDiagnostic record) arm.1 := by
    rw [serviced.arrival_eq arm]
    exact hraw.symm
  have hqueueRecord :
      liveDiagnosticQueueRecord r.payload arm.1 record = (true, serviced.arrival arm) := by
    simp [liveDiagnosticQueueRecord, henabled, harrival]
  have htake : liveDiagnosticQueueRecords r.payload arm.1 window (count + 1) =
      liveDiagnosticQueueRecords r.payload arm.1 window count ++
        [liveDiagnosticQueueRecord r.payload arm.1 record] := by
    unfold liveDiagnosticQueueRecords
    rw [(List.take_append_getElem hindex).symm, List.map_append, hrecord]
    simp
  have htransition := CoordinatorLiveServiceFinish.serviced_queueReplay_transition
    r q serviced arm
  have htransition' :
      QueueReplay.transition (4 * r.payload.n)
          (QueueReplay.replay (4 * r.payload.n) (0, 0)
            (liveDiagnosticQueueRecords r.payload arm.1 window count))
          (liveDiagnosticQueueRecord r.payload arm.1 record) =
        (serviced.score arm, serviced.queue arm) := by
    rw [← hstate, hqueueRecord]
    exact htransition
  have hpreviousStep :
      serviced.previousService arm =
        RecordedQueueRun.recordService (4 * r.payload.n)
          (QueueReplay.replay (4 * r.payload.n) (0, 0)
            (liveDiagnosticQueueRecords r.payload arm.1 window count))
          (liveDiagnosticQueueRecord r.payload arm.1 record) := by
    rw [serviced.previousService_eq arm, serviced.service_eq arm]
    have hqueue := congrArg Prod.snd hstate
    have hqueue' : q.queue arm =
        (QueueReplay.replay (4 * r.payload.n) (0, 0)
          (liveDiagnosticQueueRecords r.payload arm.1 window count)).2 := by
      simpa using hqueue
    rw [hqueue', hqueueRecord]
    simp [RecordedQueueRun.recordService, CappedService.service]
  constructor
  · calc
      (nextScore arm, nextQueue arm) = (serviced.score arm, serviced.queue arm) := by
        rw [hnextScore, hnextQueue]
      _ = QueueReplay.transition (4 * r.payload.n)
          (QueueReplay.replay (4 * r.payload.n) (0, 0)
            (liveDiagnosticQueueRecords r.payload arm.1 window count))
          (liveDiagnosticQueueRecord r.payload arm.1 record) := htransition'.symm
      _ = QueueReplay.replay (4 * r.payload.n) (0, 0)
          (liveDiagnosticQueueRecords r.payload arm.1 window (count + 1)) := by
        rw [htake, QueueReplay.replay_append]
        simp [QueueReplay.replay]
  · calc
      nextPrevious arm = serviced.previousService arm := hnextPrevious
      _ = RecordedQueueRun.recordService (4 * r.payload.n)
          (QueueReplay.replay (4 * r.payload.n) (0, 0)
            (liveDiagnosticQueueRecords r.payload arm.1 window count))
          (liveDiagnosticQueueRecord r.payload arm.1 record) := hpreviousStep
      _ = CollectionKnownQueueContinuation.replayLastService (4 * r.payload.n) (0, 0) 0
          (liveDiagnosticQueueRecords r.payload arm.1 window (count + 1)) := by
        rw [htake]
        exact (replayLastService_append_one (4 * r.payload.n) (0, 0) 0
          (liveDiagnosticQueueRecords r.payload arm.1 window count)
          (liveDiagnosticQueueRecord r.payload arm.1 record)).symm

private theorem noCutoff_start_saved_prior_false
    (time stamp sigma : Fin p.T)
    (clock : CoordinatorPhaseClock.ClockRegisters p)
    (pending : Finset (Fin (p.m - 1)))
    (result : CoordinatorPhaseClock.StartRoundResult p)
    (bit : Bool)
    (hparam : CoordinatorPhaseClock.proposalParameterValid p rate.eta.val)
    (hclock : CoordinatorPhaseClock.clockRegistersValid p rate.eta.val clock)
    (htime : CoordinatorPhaseClock.startRoundTimeValid p time clock)
    (hstart : CoordinatorPhaseClock.startRound p rate.eta.val time clock pending = .ok result)
    (hcommand : result.ledgerCommand = none)
    (hsigma : clock.sigma = some sigma) (hu : clock.u = none)
    (hnotgrid : FollowerCutoffScan.calendarRound time ≠ clock.g)
    (hproposal : clock.lastProposal = some (stamp, bit))
    (hstamp : stamp.val + 1 = time.val) :
    bit = false := by
  have hnoCut : ∀ cutoff (hcutSigma : clock.sigma = some cutoff),
      CoordinatorPhaseClock.detectCutoff clock time ≠
        .ok (.cutoff cutoff hcutSigma) := by
    intro cutoff hcutSigma hdetect
    obtain ⟨expected, hstartExpected, _, _, hcommandExpected, _⟩ :=
      CoordinatorPhaseClock.startRound_cutoff_effect p rate.eta.val time cutoff
        clock pending hparam hclock htime hcutSigma hdetect
    have heq : expected = result := Except.ok.inj (hstartExpected.symm.trans hstart)
    have hcommands := congrArg CoordinatorPhaseClock.StartRoundResult.ledgerCommand heq
    rw [hcommandExpected, hcommand] at hcommands
    cases hcommands
  have hdetect :
      CoordinatorPhaseClock.detectCutoff clock time = .ok .noCutoff := by
    cases hdecision : CoordinatorPhaseClock.detectCutoff clock time with
    | error failure =>
        simp [CoordinatorPhaseClock.startRound, hparam, hclock, htime, hdecision] at hstart
    | ok decision =>
        cases decision with
        | noCutoff => rfl
        | cutoff cutoff hcutSigma => exact False.elim (hnoCut cutoff hcutSigma hdecision)
  have hprior : CoordinatorPhaseClock.savedPriorProposal clock time = .ok bit :=
    CoordinatorPhaseClock.savedPriorProposal_correct
      clock time stamp bit hproposal hstamp
  have hsaved : CoordinatorPhaseClock.savedPriorProposal clock time = .ok false := by
    cases bit with
    | false => exact hprior
    | true =>
        have hdecision : CoordinatorPhaseClock.detectCutoff clock time =
            .ok (.cutoff sigma hsigma) := by
          rcases clock with ⟨s, u, g, token⟩
          change s = some sigma at hsigma
          change u = none at hu
          subst s
          subst u
          change token = some (stamp, true) at hproposal
          subst token
          simp [CoordinatorPhaseClock.detectCutoff,
            CoordinatorPhaseClock.savedPriorProposal, hnotgrid, hstamp]
          rfl
        rw [hdecision] at hdetect
        cases hdetect
  exact Except.ok.inj (hprior.symm.trans hsaved)

private def continuingResultPair {p : Parameters}
    {x : CoordinatorRoundDispatch.LiveInput p}
    (outcome : CoordinatorRoundDispatch.LiveOutcome x) :
    Option (CoordinatorPhaseClock.StartRoundResult p ×
      CoordinatorPhaseClock.StartRoundResult p) :=
  match outcome with
  | .continuingChosen dispatched _ continuation _ =>
      some (dispatched.startResult, continuation.startRoundResult)
  | _ => none

private theorem dispatchLive_continuation_projection
    {p : Parameters} {x : CoordinatorRoundDispatch.LiveInput p}
    (dispatched : CoordinatorStartRoundCutoffDispatch.Output
      x.registers x.ownedRegisters x.followerBaseScore)
    (continuation : CoordinatorLiveChoiceRecorderStep.Continuation x.registers x.row)
    (selection : CoordinatorRoundDispatch.ArmSelection x.registers.payload
      dispatched.startResult x.registers.time x.registers.complementWeights x.row)
    (hstart : CoordinatorPhaseClock.startRound p x.eta.val x.registers.time
      x.registers.priorClock x.registers.clockPending = .ok dispatched.startResult)
    (hactual : CoordinatorRoundDispatch.dispatchLive x =
      .continuingChosen dispatched hstart continuation selection) :
    continuation.startRoundResult = dispatched.startResult := by
  unfold CoordinatorRoundDispatch.dispatchLive at hactual
  dsimp only at hactual
  repeat' (first | split at hactual <;> try cases hactual)
  case h_3 =>
    rename_i actualDispatched hdispatch hinitialization
    by_cases hframe : CoordinatorLiveChoiceRecorderStep.unchangedLiveClockFrame
        x.registers actualDispatched.startResult
    · simp only [dite_eq_left hframe] at hactual
      by_cases hpayload : x.registers.priorClock.sigma = some x.registers.payload.sigma
      · simp only [dite_eq_left hpayload] at hactual
        by_cases hgrid : x.registers.gridBoundary = x.registers.priorClock.g
        · simp only [dite_eq_left hgrid] at hactual
          by_cases hscore : x.registers.scoreDomainValid
          · simp only [dite_eq_left hscore] at hactual
            by_cases hqueue : x.ownedRegisters.queueDomainValid
            · simp only [dite_eq_left hqueue] at hactual
              by_cases hprevious : x.ownedRegisters.previousServiceDomainValid
              · simp only [dite_eq_left hprevious] at hactual
                by_cases hbase : ∀ i, x.followerBaseScore i ≤ p.T * D p
                · simp only [dite_eq_left hbase] at hactual
                  by_cases hlive : CoordinatorLocalArmChoice.assignmentIsLive
                      x.registers.payload
                      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p
                        actualDispatched.startResult.clock.u) x.registers.time
                  · simp only [dite_eq_left hlive] at hactual
                    by_cases hchoice : CoordinatorLocalArmChoice.ChoiceInputsValid
                        x.registers.payload
                        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p
                          actualDispatched.startResult.clock.u)
                        x.registers.time x.registers.complementWeights
                    · simp only [dite_eq_left hchoice] at hactual
                      by_cases hboundary : actualDispatched.startResult.clock.g ≤ p.T + 1
                      · simp only [dite_eq_left hboundary] at hactual
                        by_cases henvelope : x.registers.complementEnvelopeValid
                        · simp only [dite_eq_left henvelope] at hactual
                          have hnonempty :=
                            CoordinatorLiveChoiceRecorderStep.coordinatorArmChoice_ne_none
                              x.registers.payload actualDispatched.startResult.pending
                              (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p
                                actualDispatched.startResult.clock.u)
                              x.registers.time x.registers.complementWeights x.row hchoice
                          split at hactual
                          · rename_i hselected
                            exact False.elim (hnonempty hselected)
                          · have hp := congrArg continuingResultPair hactual
                            have hp' := by simpa only [continuingResultPair] using hp
                            have hpair := Option.some.inj hp'
                            exact
                              (congrArg Prod.snd hpair).symm.trans
                                (congrArg Prod.fst hpair)
                        · simp only [dite_eq_right henvelope] at hactual
                          cases hactual
                      · simp only [dite_eq_right hboundary] at hactual
                        cases hactual
                    · simp only [dite_eq_right hchoice] at hactual
                      cases hactual
                  · simp only [dite_eq_right hlive] at hactual
                    cases hactual
                · simp only [dite_eq_right hbase] at hactual
                  cases hactual
              · simp only [dite_eq_right hprevious] at hactual
                cases hactual
            · simp only [dite_eq_right hqueue] at hactual
              cases hactual
          · simp only [dite_eq_right hscore] at hactual
            cases hactual
        · simp only [dite_eq_right hgrid] at hactual
          cases hactual
      · simp only [dite_eq_right hpayload] at hactual
        cases hactual
    · simp only [dite_eq_right hframe] at hactual
      cases hactual
  case h_1 =>
    rename_i actualDispatched hdispatch ledger hinitialization hchoice hboundary
      henvelope hselected
    have hnonempty := CoordinatorLiveChoiceRecorderStep.coordinatorArmChoice_ne_none
      x.registers.payload actualDispatched.startResult.pending
      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p
        actualDispatched.startResult.clock.u)
      x.registers.time x.registers.complementWeights x.row hchoice
    exact False.elim (hnonempty hselected)

private theorem run_first_complement_replay_prefix
    (initial : State p rate) (rows : CompletePublicTable.CompleteRows p)
    (J : Fin (M p)) (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (active : allActiveAtStart initial start)
    (hfirst : initial.coordinator = .first) :
    ∀ k (hkcount : k ≤ count)
      (_ : k ≤ (firstWindow initial rows J rewards start count hspan active).length),
      replayInvariant rows J start k
        (firstWindow initial rows J rewards start count hspan active)
        (originalPrefix initial rows J rewards start count hspan active k hkcount).records
        (originalPrefix initial rows J rewards start count hspan active k hkcount).finalState := by
  have hseed : ReferenceCoordinatorClockDomains.clockAt rows J start initial := by
    simp [ReferenceCoordinatorClockDomains.clockAt, hfirst]
  intro k
  induction k with
  | zero =>
      intro hkcount hkwindow
      simp [replayInvariant, originalPrefix,
        ReferenceActivePhysicalHorizon.run_zero_final, hfirst]
  | succ k ih =>
      intro hkcount hkwindow
      have hkcountPrev : k ≤ count := Nat.le_trans (Nat.le_succ k) hkcount
      have hkwindowPrev : k ≤
          (firstWindow initial rows J rewards start count hspan active).length :=
        Nat.le_trans (Nat.le_succ k) hkwindow
      let runPrefix := originalPrefix initial rows J rewards start count hspan active k hkcountPrev
      let next := originalPrefix initial rows J rewards start count hspan active (k + 1) hkcount
      have hInv : replayInvariant rows J start k
          (firstWindow initial rows J rewards start count hspan active)
          runPrefix.records runPrefix.finalState := by
        simpa [runPrefix] using ih hkcountPrev hkwindowPrev
      let current := (firstWindow initial rows J rewards start count hspan active)[k]
      have hkltWindow : k <
          (firstWindow initial rows J rewards start count hspan active).length := by omega
      have hcurrentEq : current =
          ReferenceAssignmentPayloadChronology.actualRunRecordAt initial rows J rewards
            start k (by omega) active := by
        exact firstWindow_record_eq_actualRunRecordAt initial rows J rewards start count
          hspan active hfirst k (by omega) hkltWindow
      have htimeCurrent : current.input.time.val = start + k := by
        rw [hcurrentEq]
        rfl
      have hinputState : current.input.state = runPrefix.finalState := by
        simpa [current, runPrefix] using
          firstWindow_input_state_eq_prefix initial rows J rewards start count hspan
            active hfirst k hkcountPrev hkltWindow
      have hstateOut : next.finalState = current.output.next := by
        calc
          next.finalState =
              (ReferenceAssignmentPayloadChronology.actualRunRecordAt initial rows J rewards
                start k (by omega) active).output.next :=
            ReferenceAssignmentPayloadChronology.run_successor_finalState_eq_actualRunRecordAt
              initial rows J rewards start k (by omega) active
          _ = current.output.next := by rw [hcurrentEq]
      have hsuccessor := ReferenceAssignmentPayloadChronology.run_successor_actualRunRecordAt
        initial rows J rewards start k (by omega) active
      have hcurrentMemNext : current ∈ next.records := by
        change current ∈
          (ReferenceActivePhysicalHorizon.run initial rows J rewards start (k + 1)
            (by omega) active).records
        rw [hcurrentEq, hsuccessor]
        exact List.mem_append_right _ (List.mem_singleton_self _)
      have hcurrentMemWindow : current ∈
          firstWindow initial rows J rewards start count hspan active :=
        List.getElem_mem hkltWindow
      have hnotCut : ReferenceCollectionPhaseHistory.cutoffChosen current.input = false := by
        have hkeep := List.mem_takeWhile_imp hcurrentMemWindow
        simpa only [current, firstWindow,
          ReferenceFirstLiveConfirmationHistory.firstLiveWindow,
          Bool.not_eq_true'] using hkeep
      have hprepared : current.output.preparation =
          ReferenceActivePhysicalStep.prepare current.input := by
        rw [current.output_eq]
        rfl
      have hstepCoord : next.finalState.coordinator =
          current.output.preparation.observeCoordinator.configuration := by
        calc
          next.finalState.coordinator = current.output.next.coordinator :=
            congrArg (fun s : State p rate => s.coordinator) hstateOut
          _ = (ReferenceActivePhysicalStep.step current.input).next.coordinator := by
            rw [current.output_eq]
          _ = (ReferenceActivePhysicalStep.prepare current.input).observeCoordinator.configuration :=
            (ReferenceActivePhysicalStep.step_next_fields current.input).1
          _ = current.output.preparation.observeCoordinator.configuration := by
            rw [← hprepared]
      have hclockRun := ReferenceRunClockPreservation.run_clockAt initial rows J rewards
        start (k + 1) (by omega) active hseed
      have hclockNext := hclockRun.2.1 (k + 1) le_rfl
      have hclockCurrent := hclockRun.2.1 k (by omega)
      cases hcoord : runPrefix.finalState.coordinator with
      | first =>
          have hkzero : k = 0 := by
            simpa [replayInvariant, runPrefix, hcoord] using hInv
          have hinputFirst : current.input.state.coordinator = .first := by
            rw [hinputState, hcoord]
          have hprepFirst : current.output.preparation.coordinator =
              .first (CoordinatorRoundDispatch.dispatchFirst
                (ReferenceActivePhysicalStep.firstInput current.input)) := by
            rw [hprepared]
            exact ReferenceActivePhysicalStep.dispatch_first current.input hinputFirst
          cases hdispatch : CoordinatorRoundDispatch.dispatchFirst
              (ReferenceActivePhysicalStep.firstInput current.input) with
          | choiceDomainFailure installed =>
              have hcut : current.output.preparation.coordinator =
                  .first (.choiceDomainFailure installed) := by rw [hprepFirst, hdispatch]
              have hselection :
                  (ReferenceActivePhysicalStep.DispatchCut.first
                    (.choiceDomainFailure installed)).selection = none := by
                simp [ReferenceActivePhysicalStep.DispatchCut.selection]
              have hdagger := preparedFirst_noSelection_dagger current
                (.choiceDomainFailure installed) hcut hselection
              have hnextDagger : next.finalState.coordinator = .dagger :=
                hstateOut ▸ hdagger
              simp [replayInvariant, next, hnextDagger]
          | recorderBoundaryFailure installed =>
              have hcut : current.output.preparation.coordinator =
                  .first (.recorderBoundaryFailure installed) := by rw [hprepFirst, hdispatch]
              have hselection :
                  (ReferenceActivePhysicalStep.DispatchCut.first
                    (.recorderBoundaryFailure installed)).selection = none := by
                simp [ReferenceActivePhysicalStep.DispatchCut.selection]
              have hdagger := preparedFirst_noSelection_dagger current
                (.recorderBoundaryFailure installed) hcut hselection
              have hnextDagger : next.finalState.coordinator = .dagger :=
                hstateOut ▸ hdagger
              simp [replayInvariant, next, hnextDagger]
          | choiceRejected installed =>
              have hcut : current.output.preparation.coordinator =
                  .first (.choiceRejected installed) := by rw [hprepFirst, hdispatch]
              have hselection :
                  (ReferenceActivePhysicalStep.DispatchCut.first
                    (.choiceRejected installed)).selection = none := by
                simp [ReferenceActivePhysicalStep.DispatchCut.selection]
              have hdagger := preparedFirst_noSelection_dagger current
                (.choiceRejected installed) hcut hselection
              have hnextDagger : next.finalState.coordinator = .dagger :=
                hstateOut ▸ hdagger
              simp [replayInvariant, next, hnextDagger]
          | chosen installed selection =>
              have hchosenTime := ReferenceActivePhysicalStep.dispatchFirst_chosen_time
                current.input installed selection hdispatch
              have hselector :
                  (ReferenceActivePhysicalStep.DispatchCut.first
                    (.chosen installed selection)).selection ≠ none := by
                simp [ReferenceActivePhysicalStep.DispatchCut.selection,
                  ReferenceActivePhysicalStep.selectionAt, hchosenTime]
              have hcut : current.output.preparation.coordinator =
                  .first (.chosen installed selection) := by rw [hprepFirst, hdispatch]
              have hobs := ReferenceActivePhysicalStep.observeCoordinator_first_equation
                current.output.preparation (.chosen installed selection) hcut
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
              rcases ReferenceActivePhysicalStep.dispatchFirst_zero_seed
                  current.input installed selection hdispatch with
                ⟨hscore0, hqueue0, _, hbase0⟩
              let birth := ReferenceAssignmentPayloadChronology.actualStepRecord current.input
              have hbirth :
                  ReferenceAssignmentPayloadPersistence.InstallationBirth birth
                    installed.registers.payload := by
                exact ReferenceAssignmentPayloadChronology.actualFirstChosen_installationBirth
                  current.input hinputFirst installed selection hdispatch
              have hbirthEq : birth = current := by
                dsimp [birth]
                exact actualStepRecord_eq current
              have hbirthMemNext : birth ∈ next.records := by
                rw [hbirthEq]
                exact hcurrentMemNext
              have hbirthTime : birth.input.time.val = start := by
                simp [birth, ReferenceAssignmentPayloadChronology.actualStepRecord,
                  htimeCurrent, hkzero]
              have hbirthFirstChosen :
                  ∃ birthInstallation birthSelection,
                    birth.output.preparation.coordinator =
                      .first (.chosen birthInstallation birthSelection) := by
                rw [hbirthEq]
                exact ⟨installed, selection, hcut⟩
              rcases livePostChoice_success_or_dagger current.input current.output.preparation
                  installed.registers installed.ownedRegisters installed.followerBaseScore
                  installed.startRoundResult with htailDagger | ⟨recording, serviced, pending,
                    finished, hrecording, hservice, hserviceRecording, hconfirmation,
                    hfinish, htailLive⟩
              · have hnextDagger : next.finalState.coordinator = .dagger :=
                  hnextTail.trans htailDagger
                simp [replayInvariant, next, hnextDagger]
              · let nextRegisters := postChoiceRegisters installed.registers current.input
                  finished serviced
                let nextOwned := postChoiceOwned installed.registers current.input finished serviced
                have htailLive' :
                    (ReferenceActivePhysicalStep.livePostChoice current.output.preparation
                      installed.registers installed.ownedRegisters installed.followerBaseScore
                      installed.startRoundResult).configuration =
                      .live nextRegisters nextOwned installed.followerBaseScore := by
                  simpa [nextRegisters, nextOwned] using htailLive
                have hnextLive : next.finalState.coordinator =
                    .live nextRegisters nextOwned installed.followerBaseScore := hnextTail.trans htailLive'
                have hclockShape : ReferenceCoordinatorClockDomains.clockAt rows J
                    (start + (k + 1)) next.finalState := by
                  simpa [next, originalPrefix] using hclockNext
                have hboundary := live_clock_boundary_eq rows J (start + (k + 1))
                  next.finalState nextRegisters nextOwned installed.followerBaseScore
                  hnextLive hclockShape
                have hboundaryPayload : nextRegisters.gridBoundary =
                    FollowerCutoffScan.gridBoundary p rate.eta.val
                      installed.registers.payload.sigma := by
                  simpa [nextRegisters, postChoiceRegisters] using hboundary
                simp only [ReferenceCoordinatorClockDomains.clockAt, hnextLive] at hclockShape
                rcases hclockShape with ⟨_, _, _, _, _, _, hstrict, _⟩
                have hactualRecording := livePostChoice_actual_recording current
                  current.output.preparation installed.registers installed.ownedRegisters
                  installed.followerBaseScore installed.startRoundResult rfl htail
                  recording hrecording
                have hactualServicedRecording :
                    current.output.coordinator.recording = some serviced.recording := by
                  rw [hactualRecording, hserviceRecording]
                have henabled : decide (current.input.time.val + 1 <
                    FollowerCutoffScan.gridBoundary p rate.eta.val installed.registers.payload.sigma) = true := by
                  apply decide_eq_true_eq.mpr
                  rw [← hboundaryPayload]
                  rw [htimeCurrent]
                  omega
                have hallEnabledNext : ∀ a : FastArm installed.registers.payload.slowSet,
                    ∀ record ∈ (firstWindow initial rows J rewards start count hspan active).take
                        (k + 1),
                      (liveDiagnosticQueueRecord installed.registers.payload a.1 record).1 = true := by
                  intro a
                  have hpreviousEnabled :
                      ∀ record ∈ (firstWindow initial rows J rewards start count hspan active).take k,
                        (liveDiagnosticQueueRecord installed.registers.payload a.1 record).1 = true := by
                    intro record hrecord
                    simp [hkzero] at hrecord
                  have hcurrentEnabled :
                      (liveDiagnosticQueueRecord installed.registers.payload a.1
                        (firstWindow initial rows J rewards start count hspan active)[k]).1 = true := by
                    simpa [current, liveDiagnosticQueueRecord] using henabled
                  exact liveDiagnosticRecords_enabled_take_succ installed.registers.payload a
                    (firstWindow initial rows J rewards start count hspan active) k
                    hkltWindow hpreviousEnabled hcurrentEnabled
                have hbaseNext : ∀ i, installed.followerBaseScore i = 0 := hbase0
                have hproposalHistoryNext :
                    ∀ i : Fin p.T, start ≤ i.val →
                      i.val + 1 < start + (k + 1) →
                      FollowerCutoffScan.completeRowProposalBit p rate.eta.val
                        (rows J) i = false := by
                  intro i hiStart hiBefore
                  omega
                have hwindowReplay : ∀ a : FastArm installed.registers.payload.slowSet,
                    (nextRegisters.complementScores a, nextOwned.queue a) =
                      QueueReplay.replay (4 * installed.registers.payload.n) (0, 0)
                        (liveDiagnosticQueueRecords installed.registers.payload a.1
                          (firstWindow initial rows J rewards start count hspan active) (k + 1)) ∧
                    nextOwned.previousService a =
                      CollectionKnownQueueContinuation.replayLastService
                        (4 * installed.registers.payload.n) (0, 0) 0
                        (liveDiagnosticQueueRecords installed.registers.payload a.1
                          (firstWindow initial rows J rewards start count hspan active) (k + 1)) := by
                  intro a
                  have hbaseReplay :
                      liveDiagnosticQueueRecords installed.registers.payload a.1
                        (firstWindow initial rows J rewards start count hspan active) k = [] := by
                    simp [liveDiagnosticQueueRecords, hkzero]
                  have hstate :
                      (installed.registers.complementScores a, installed.ownedRegisters.queue a) =
                        QueueReplay.replay (4 * installed.registers.payload.n) (0, 0)
                          (liveDiagnosticQueueRecords installed.registers.payload a.1
                            (firstWindow initial rows J rewards start count hspan active) k) := by
                    rw [hscore0 a, hqueue0 a, hbaseReplay]
                    rfl
                  exact diagnostic_serviced_extension
                    (firstWindow initial rows J rewards start count hspan active) k current
                    hkltWindow rfl installed.registers installed.ownedRegisters serviced a
                    nextRegisters.complementScores nextOwned.queue nextOwned.previousService
                    hstate rfl rfl rfl hactualServicedRecording henabled
                simp only [replayInvariant, next, hnextLive]
                exact ⟨hbaseNext,
                  ⟨birth, hbirthMemNext, hbirth, hbirthTime,
                    hbirthFirstChosen⟩,
                  hproposalHistoryNext, hallEnabledNext, hwindowReplay⟩
      | collection payload ledger proposal =>
          simp only [replayInvariant, hcoord] at hInv
      | dagger =>
          have hinputDagger : current.input.state.coordinator = .dagger := by
            rw [hinputState, hcoord]
          have hdagger : next.finalState.coordinator = .dagger := by
            calc
              next.finalState.coordinator = current.output.preparation.observeCoordinator.configuration :=
                hstepCoord
              _ = .dagger := by
                rw [hprepared]
                simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
                  ReferenceActivePhysicalStep.prepare,
                  ReferenceActivePhysicalStep.dispatch, hinputDagger,
                  ReferenceActivePhysicalStep.DispatchCut.selection]
          simp [replayInvariant, next, hdagger]
      | live oldRegisters oldOwned oldBase =>
          simp only [replayInvariant, hcoord] at hInv
          rcases hInv with ⟨hbaseOld, ⟨birth, hbirthMem, hbirth, hbirthTime,
            hbirthFirstChosen⟩, hproposalHistoryOld,
            henabledOld, hreplayOld⟩
          have hinputLive : current.input.state.coordinator =
              .live oldRegisters oldOwned oldBase := by
            rw [hinputState, hcoord]
          let outcome := CoordinatorRoundDispatch.dispatchLive
            (ReferenceActivePhysicalStep.liveInput current.input oldRegisters oldOwned oldBase)
          have hprepLive : current.output.preparation.coordinator =
              .live oldRegisters oldOwned oldBase outcome := by
            rw [hprepared]
            change ReferenceActivePhysicalStep.dispatch current.input = _
            rw [ReferenceActivePhysicalStep.dispatch, hinputLive]
            rfl
          have hprepLive' :
              (ReferenceActivePhysicalStep.prepare current.input).coordinator =
                .live oldRegisters oldOwned oldBase outcome := by
            rw [← hprepared]
            exact hprepLive
          have hobs := ReferenceActivePhysicalStep.observeCoordinator_live_equation
            current.output.preparation oldRegisters oldOwned oldBase outcome hprepLive
          cases hdispatch : outcome with
          | cutoffChosen dispatched hstart ledger hinit ledgerCandidate hdomains hclock
              hpending hnostart selection =>
              have hchosenCut :
                  ReferenceCollectionPhaseHistory.cutoffChosen current.input = true := by
                have hprepLiveCase := hprepLive'
                rw [hdispatch] at hprepLiveCase
                unfold ReferenceCollectionPhaseHistory.cutoffChosen
                rw [hprepLiveCase]
              have hfalse : true = false := hchosenCut.symm.trans hnotCut
              cases hfalse
          | continuingChosen dispatched hstart continuation selection =>
              have hprepLiveCase := hprepLive'
              rw [hdispatch] at hprepLiveCase
              by_cases hselector :
                  (ReferenceActivePhysicalStep.DispatchCut.live oldRegisters oldOwned
                    oldBase (.continuingChosen dispatched hstart continuation selection)).selection = none
              · have hdagger : next.finalState.coordinator = .dagger := by
                  have hstepDagger := ReferenceLiveClockPreservation.step_live_noChoice_dagger
                    oldRegisters oldOwned oldBase
                    (.continuingChosen dispatched hstart continuation selection)
                    hprepLiveCase hselector
                  calc
                    next.finalState.coordinator = current.output.next.coordinator :=
                      congrArg (fun s : State p rate => s.coordinator) hstateOut
                    _ = (ReferenceActivePhysicalStep.step current.input).next.coordinator := by
                      rw [current.output_eq]
                    _ = .dagger := hstepDagger.1
                simp [replayInvariant, next, hdagger]
              · let actualRegisters := ReferenceActivePhysicalStep.liveRegistersAt
                  oldRegisters current.input.time
                let actualOwned := ReferenceActivePhysicalStep.liveOwnedAt
                  oldRegisters oldOwned current.input.time
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
                rcases livePostChoice_success_or_dagger current.input current.output.preparation
                    actualRegisters actualOwned oldBase dispatched.startResult with
                  htailDagger | ⟨recording, serviced, pending, finished,
                    hrecording, hservice, hserviceRecording, hconfirmation, hfinish, htailLive⟩
                · have hnextDagger : next.finalState.coordinator = .dagger :=
                    hnextTail.trans htailDagger
                  simp [replayInvariant, next, hnextDagger]
                · let nextRegisters := postChoiceRegisters actualRegisters current.input
                    finished serviced
                  let nextOwned := postChoiceOwned actualRegisters current.input finished serviced
                  have htailLive' :
                      (ReferenceActivePhysicalStep.livePostChoice current.output.preparation
                        actualRegisters actualOwned oldBase dispatched.startResult).configuration =
                        .live nextRegisters nextOwned oldBase := by
                    simpa [nextRegisters, nextOwned] using htailLive
                  have hnextLive : next.finalState.coordinator =
                      .live nextRegisters nextOwned oldBase := hnextTail.trans htailLive'
                  have hclockShape : ReferenceCoordinatorClockDomains.clockAt rows J
                      (start + (k + 1)) next.finalState := by
                    simpa [next, originalPrefix] using hclockNext
                  have hboundary := live_clock_boundary_eq rows J (start + (k + 1))
                    next.finalState nextRegisters nextOwned oldBase hnextLive hclockShape
                  have hboundaryPayload : nextRegisters.gridBoundary =
                      FollowerCutoffScan.gridBoundary p rate.eta.val oldRegisters.payload.sigma := by
                    simpa [nextRegisters, postChoiceRegisters, actualRegisters,
                      ReferenceActivePhysicalStep.liveRegistersAt] using hboundary
                  simp only [ReferenceCoordinatorClockDomains.clockAt, hnextLive] at hclockShape
                  rcases hclockShape with ⟨_, _, _, _, _, _, hstrict, _⟩
                  have hclockPrefix : ReferenceCoordinatorClockDomains.clockAt rows J
                      (start + k) runPrefix.finalState := by
                    simpa [runPrefix, originalPrefix] using hclockCurrent
                  simp only [ReferenceCoordinatorClockDomains.clockAt, hcoord] at hclockPrefix
                  rcases hclockPrefix with ⟨hregisterTime, hclockValid, hclockSigma,
                    hclockU, hclockGrid, hsigmaTime, hclockBeforeGrid,
                    hproposalPrevious⟩
                  have hboundaryOld := live_clock_boundary_eq rows J (start + k)
                    runPrefix.finalState oldRegisters oldOwned oldBase hcoord hclockCurrent
                  have hnextTime : nextRegisters.time.val = current.input.time.val := by
                    simp [nextRegisters, postChoiceRegisters, actualRegisters,
                      ReferenceActivePhysicalStep.liveRegistersAt]
                  have hboundaryEq : nextRegisters.gridBoundary =
                      oldRegisters.priorClock.g := by
                    calc
                      nextRegisters.gridBoundary =
                          FollowerCutoffScan.gridBoundary p rate.eta.val
                            oldRegisters.payload.sigma := hboundaryPayload
                      _ = oldRegisters.gridBoundary := hboundaryOld.symm
                      _ = oldRegisters.priorClock.g := hclockGrid
                  have hnotgrid : FollowerCutoffScan.calendarRound current.input.time ≠
                      oldRegisters.priorClock.g := by
                    intro heq
                    have hstrictCurrent : current.input.time.val + 1 <
                        oldRegisters.priorClock.g := by
                      calc
                        current.input.time.val + 1 = start + (k + 1) := by
                          rw [htimeCurrent]
                          omega
                        _ < nextRegisters.gridBoundary := hstrict
                        _ = oldRegisters.priorClock.g := hboundaryEq
                    unfold FollowerCutoffScan.calendarRound at heq
                    omega
                  have hstartValid : CoordinatorPhaseClock.startRoundTimeValid p
                      current.input.time oldRegisters.priorClock := by
                    simp only [CoordinatorPhaseClock.startRoundTimeValid,
                      hclockSigma, hclockU, FollowerCutoffScan.calendarRound]
                    omega
                  have hstartCurrent : CoordinatorPhaseClock.startRound p rate.eta.val
                      current.input.time oldRegisters.priorClock oldRegisters.clockPending =
                        .ok dispatched.startResult := by
                    simpa [ReferenceActivePhysicalStep.liveInput,
                      ReferenceActivePhysicalStep.liveRegistersAt,
                      CoordinatorLiveChoiceRecorderStep.Registers.clockPending_eq]
                      using hstart
                  have hcontinuationResult :
                      continuation.startRoundResult = dispatched.startResult := by
                    have hactual : CoordinatorRoundDispatch.dispatchLive
                        (ReferenceActivePhysicalStep.liveInput current.input oldRegisters
                          oldOwned oldBase) =
                          .continuingChosen dispatched hstart continuation selection := by
                      simpa [outcome] using hdispatch
                    apply dispatchLive_continuation_projection
                      dispatched continuation selection ?_ hactual
                    simpa [ReferenceActivePhysicalStep.liveInput,
                      ReferenceActivePhysicalStep.liveRegistersAt] using hstart
                  have hcommand : dispatched.startResult.ledgerCommand = none := by
                    rw [← hcontinuationResult]
                    exact continuation.clockFrame.2.2.1
                  have hproposalPreviousFalse := noCutoff_start_saved_prior_false
                    current.input.time oldRegisters.time oldRegisters.payload.sigma
                    oldRegisters.priorClock oldRegisters.clockPending dispatched.startResult
                    (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
                      (rows J) oldRegisters.time)
                    (ReferenceCoordinatorClockDomains.proposalParameterValid_of_rate rate)
                    hclockValid hstartValid hstartCurrent hcommand hclockSigma hclockU
                    hnotgrid hproposalPrevious (by rw [htimeCurrent]; omega)
                  have hproposalHistoryNext :
                      ∀ i : Fin p.T, start ≤ i.val →
                        i.val + 1 < start + (k + 1) →
                        FollowerCutoffScan.completeRowProposalBit p rate.eta.val
                          (rows J) i = false := by
                    intro i hiStart hiBefore
                    by_cases hiOld : i.val + 1 < start + k
                    · exact hproposalHistoryOld i hiStart hiOld
                    · have hiBoundary : i.val + 1 = start + k := by omega
                      have hiPrevious : i = oldRegisters.time := by
                        apply Fin.ext
                        omega
                      rw [hiPrevious]
                      exact hproposalPreviousFalse
                  have hactualRecording := livePostChoice_actual_recording current
                    current.output.preparation actualRegisters actualOwned oldBase
                    dispatched.startResult rfl htail recording hrecording
                  have hactualServicedRecording :
                      current.output.coordinator.recording = some serviced.recording := by
                    rw [hactualRecording, hserviceRecording]
                  have henabled : decide (current.input.time.val + 1 <
                      FollowerCutoffScan.gridBoundary p rate.eta.val oldRegisters.payload.sigma) = true := by
                    apply decide_eq_true_eq.mpr
                    rw [← hboundaryPayload]
                    rw [htimeCurrent]
                    omega
                  have hallEnabledNext : ∀ a : FastArm oldRegisters.payload.slowSet,
                      ∀ record ∈ (firstWindow initial rows J rewards start count hspan active).take
                          (k + 1),
                        (liveDiagnosticQueueRecord oldRegisters.payload a.1 record).1 = true := by
                    intro a
                    have hcurrentEnabled :
                        (liveDiagnosticQueueRecord oldRegisters.payload a.1
                          (firstWindow initial rows J rewards start count hspan active)[k]).1 = true := by
                      simpa [current, liveDiagnosticQueueRecord] using henabled
                    exact liveDiagnosticRecords_enabled_take_succ oldRegisters.payload a
                      (firstWindow initial rows J rewards start count hspan active) k
                      hkltWindow (henabledOld a) hcurrentEnabled
                  have hbaseNext : ∀ i, oldBase i = 0 := hbaseOld
                  have hwindowReplay : ∀ a : FastArm oldRegisters.payload.slowSet,
                      (nextRegisters.complementScores a, nextOwned.queue a) =
                        QueueReplay.replay (4 * oldRegisters.payload.n) (0, 0)
                          (liveDiagnosticQueueRecords oldRegisters.payload a.1
                            (firstWindow initial rows J rewards start count hspan active) (k + 1)) ∧
                      nextOwned.previousService a =
                        CollectionKnownQueueContinuation.replayLastService
                          (4 * oldRegisters.payload.n) (0, 0) 0
                          (liveDiagnosticQueueRecords oldRegisters.payload a.1
                            (firstWindow initial rows J rewards start count hspan active) (k + 1)) := by
                    intro a
                    have hstate := hreplayOld a
                    have hstate' :
                        (actualRegisters.complementScores a, actualOwned.queue a) =
                          QueueReplay.replay (4 * oldRegisters.payload.n) (0, 0)
                            (liveDiagnosticQueueRecords oldRegisters.payload a.1
                              (firstWindow initial rows J rewards start count hspan active) k) := by
                      simpa [actualRegisters, actualOwned,
                        ReferenceActivePhysicalStep.liveRegistersAt,
                        ReferenceActivePhysicalStep.liveOwnedAt] using hstate.1
                    exact diagnostic_serviced_extension
                      (firstWindow initial rows J rewards start count hspan active) k current
                      hkltWindow rfl actualRegisters actualOwned serviced a
                      nextRegisters.complementScores nextOwned.queue nextOwned.previousService
                      hstate' rfl rfl rfl hactualServicedRecording henabled
                  have hbirthMemNext : birth ∈ next.records := by
                    change birth ∈
                      (ReferenceActivePhysicalHorizon.run initial rows J rewards start (k + 1)
                        (by omega) active).records
                    rw [ReferenceAssignmentPayloadChronology.run_successor_actualRunRecordAt
                      initial rows J rewards start k (by omega) active]
                    exact List.mem_append_left _ hbirthMem
                  simp only [replayInvariant, next, hnextLive]
                  exact ⟨hbaseNext,
                    ⟨birth, hbirthMemNext, hbirth, hbirthTime,
                      hbirthFirstChosen⟩,
                    hproposalHistoryNext, hallEnabledNext, hwindowReplay⟩
          | clockFailure failure hfailure =>
              have hprepLiveCase := hprepLive'
              rw [hdispatch] at hprepLiveCase
              have hselection :
                  (ReferenceActivePhysicalStep.DispatchCut.live oldRegisters oldOwned oldBase
                    (.clockFailure failure hfailure)).selection = none := by
                simp [ReferenceActivePhysicalStep.DispatchCut.selection]
              have hstepDagger := ReferenceLiveClockPreservation.step_live_noChoice_dagger
                oldRegisters oldOwned oldBase (.clockFailure failure hfailure)
                hprepLiveCase hselection
              have hnextDagger : next.finalState.coordinator = .dagger := by
                calc
                  next.finalState.coordinator = current.output.next.coordinator :=
                    congrArg (fun s : State p rate => s.coordinator) hstateOut
                  _ = (ReferenceActivePhysicalStep.step current.input).next.coordinator := by
                    rw [current.output_eq]
                  _ = .dagger := hstepDagger.1
              simp [replayInvariant, next, hnextDagger]
          | initializerFailure dispatched hstart checked hchecked =>
              have hprepLiveCase := hprepLive'
              rw [hdispatch] at hprepLiveCase
              have hselection :
                  (ReferenceActivePhysicalStep.DispatchCut.live oldRegisters oldOwned oldBase
                    (.initializerFailure dispatched hstart checked hchecked)).selection = none := by
                simp [ReferenceActivePhysicalStep.DispatchCut.selection]
              have hstepDagger := ReferenceLiveClockPreservation.step_live_noChoice_dagger
                oldRegisters oldOwned oldBase
                (.initializerFailure dispatched hstart checked hchecked) hprepLiveCase hselection
              have hnextDagger : next.finalState.coordinator = .dagger := by
                calc
                  next.finalState.coordinator = current.output.next.coordinator :=
                    congrArg (fun s : State p rate => s.coordinator) hstateOut
                  _ = (ReferenceActivePhysicalStep.step current.input).next.coordinator := by
                    rw [current.output_eq]
                  _ = .dagger := hstepDagger.1
              simp [replayInvariant, next, hnextDagger]
          | localFailure dispatched hstart reason =>
              have hprepLiveCase := hprepLive'
              rw [hdispatch] at hprepLiveCase
              have hselection :
                  (ReferenceActivePhysicalStep.DispatchCut.live oldRegisters oldOwned oldBase
                    (.localFailure dispatched hstart reason)).selection = none := by
                simp [ReferenceActivePhysicalStep.DispatchCut.selection]
              have hstepDagger := ReferenceLiveClockPreservation.step_live_noChoice_dagger
                oldRegisters oldOwned oldBase (.localFailure dispatched hstart reason)
                hprepLiveCase hselection
              have hnextDagger : next.finalState.coordinator = .dagger := by
                calc
                  next.finalState.coordinator = current.output.next.coordinator :=
                    congrArg (fun s : State p rate => s.coordinator) hstateOut
                  _ = (ReferenceActivePhysicalStep.step current.input).next.coordinator := by
                    rw [current.output_eq]
                  _ = .dagger := hstepDagger.1
              simp [replayInvariant, next, hnextDagger]

/-- The public endpoint is an enabled zero-seeded replay of the retained
first-live diagnostic prefix. The witness keeps the actual first `.chosen`
constructor and its whole installed payload. This says nothing about physical
recorder truth or a common full-horizon queue run. -/
theorem run_first_complement_replay
    (initial : State p rate) (rows : CompletePublicTable.CompleteRows p)
    (J : Fin (M p)) (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (active : allActiveAtStart initial start)
    (hfirst : initial.coordinator = .first)
    (k : ℕ) (hkcount : k ≤ count)
    (hkwindow : k ≤
      (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (ReferenceActivePhysicalHorizon.run initial rows J rewards start count hspan active).records).length)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ)
    (hlive : (ReferenceActivePhysicalHorizon.run initial rows J rewards start k
      (by omega) active).finalState.coordinator = .live r q base) :
    k > 0 ∧
      r.payload.sigma.val = start ∧
      (∀ i, base i = 0) ∧
      (∃ birth : RoundRecord p rate,
        birth ∈ (ReferenceActivePhysicalHorizon.run initial rows J rewards start k
          (by omega) active).records ∧
        ReferenceAssignmentPayloadPersistence.InstallationBirth birth r.payload ∧
        birth.input.time.val = start ∧
        (∃ installed selection,
          birth.output.preparation.coordinator = .first (.chosen installed selection) ∧
          installed.registers.payload = r.payload)) ∧
      (∀ i : Fin p.T, start ≤ i.val → i.val + 1 < start + k →
        FollowerCutoffScan.completeRowProposalBit p rate.eta.val (rows J) i = false) ∧
      (∀ a : FastArm r.payload.slowSet,
        let D := liveDiagnosticQueueRecords r.payload a.1
          (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
            (ReferenceActivePhysicalHorizon.run initial rows J rewards start count hspan active).records) k
        D.length = k ∧
        (∀ d ∈ D, d.1 = true) ∧
        (r.complementScores a, q.queue a) =
          QueueReplay.replay (4 * r.payload.n) (0, 0) D ∧
        q.previousService a =
          CollectionKnownQueueContinuation.replayLastService
            (4 * r.payload.n) (0, 0) 0 D) := by
  have hinvariant := run_first_complement_replay_prefix initial rows J rewards start count
    hspan active hfirst k hkcount hkwindow
  have hinvariantRun : replayInvariant rows J start k
      (firstWindow initial rows J rewards start count hspan active)
      (ReferenceActivePhysicalHorizon.run initial rows J rewards start k
        (by omega) active).records
      (ReferenceActivePhysicalHorizon.run initial rows J rewards start k
        (by omega) active).finalState := by
    simpa [originalPrefix] using hinvariant
  simp only [replayInvariant, hlive] at hinvariantRun
  rcases hinvariantRun with ⟨hbase, ⟨birth, hbirthMem, hbirth, hbirthTime,
    hbirthFirstChosen⟩, hproposalHistory, henabled, hreplay⟩
  have hkpositive : k > 0 := by
    by_contra hnot
    have hkzero : k = 0 := by omega
    have hfinal : (ReferenceActivePhysicalHorizon.run initial rows J rewards start k
        (by omega) active).finalState = initial := by
      simpa [hkzero] using ReferenceActivePhysicalHorizon.run_zero_final
        initial rows J rewards start (by omega) active
    rw [hfinal, hfirst] at hlive
    cases hlive
  have hsigma : r.payload.sigma.val = start := by
    exact (ReferenceAssignmentPayloadChronology.installationBirth_time_eq birth
      r.payload hbirth).trans hbirthTime
  obtain ⟨installed, selection, hchosen⟩ := hbirthFirstChosen
  have hwhole : installed.registers.payload = r.payload := by
    have hborn := hbirth
    rw [ReferenceAssignmentPayloadPersistence.InstallationBirth, hchosen] at hborn
    exact hborn.1.symm
  refine ⟨hkpositive, hsigma, hbase,
    ⟨birth, hbirthMem, hbirth, hbirthTime, installed, selection, hchosen, hwhole⟩,
    hproposalHistory, ?_⟩
  intro a
  let D := liveDiagnosticQueueRecords r.payload a.1
    (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceActivePhysicalHorizon.run initial rows J rewards start count hspan active).records) k
  have hlength : D.length = k := by
    simp [D, liveDiagnosticQueueRecords, Nat.min_eq_left hkwindow]
  have hall : ∀ d ∈ D, d.1 = true := by
    intro d hd
    rcases List.mem_map.mp hd with ⟨record, hrecord, rfl⟩
    exact henabled a record hrecord
  have hstate := hreplay a
  have hstate' :
      (r.complementScores a, q.queue a) =
          QueueReplay.replay (4 * r.payload.n) (0, 0) D ∧
        q.previousService a =
          CollectionKnownQueueContinuation.replayLastService
            (4 * r.payload.n) (0, 0) 0 D := by
    simpa [D, firstWindow, originalRun] using hstate
  exact ⟨hlength, hall, hstate'⟩

end Bandits.Support.ReferenceFirstComplementReplay

end
