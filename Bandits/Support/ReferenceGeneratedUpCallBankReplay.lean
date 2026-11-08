/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedUpBatchCalendar

/-!
# Actual UP calls on generated bank-replay runs

Sources: `sources/zip4/manuscript/appendix_a_local_protocol.tex:112-157`,
`sources/zip4/manuscript/05_binary_transport.tex:20-42,70-124`,
`sources/zip4/manuscript/06_interruptions.tex:277-284,327-348`, and
`sources/zip4/manuscript/07_public_setup.tex:121-164`.

These internal results connect an executed diagnostic on the original
generated physical run to its exact incoming prefix, actual decoder call, and
physical bank commit. A surviving-successor conclusion is kept conditional on
that actual successor; no reset interval or regret theorem is asserted.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferenceCoordinatorUpDecoderReplay
open Bandits.Support.CoordinatorUpReception
open Bandits.Support.AffineBatchDecoder

namespace Bandits.Support.ReferenceGeneratedUpCallBankReplay

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev TimeControl := ContinuousLearningRows.TimeControl

variable {p : Parameters} {rate : RateInput p}

private theorem foldCalendar_records_take_acc
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start : ℕ) (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (entries : List (ReferenceActivePhysicalHorizon.CalendarEntry p start))
    (acc : ReferenceActivePhysicalHorizon.Run initial) :
    (entries.foldl
      (ReferenceActivePhysicalHorizon.foldRound initial rows selected rewards start hmode)
      acc).records.take acc.records.length = acc.records := by
  induction entries generalizing acc with
  | nil => simp
  | cons entry entries ih =>
      change ((entries.foldl
        (ReferenceActivePhysicalHorizon.foldRound initial rows selected rewards start hmode)
        (ReferenceActivePhysicalHorizon.foldRound initial rows selected rewards start hmode
          acc entry)).records).take acc.records.length = acc.records
      let next := ReferenceActivePhysicalHorizon.foldRound initial rows selected rewards start hmode
        acc entry
      have htail := ih (acc := next)
      have hlen : acc.records.length ≤ next.records.length := by
        simp [next, ReferenceActivePhysicalHorizon.foldRound]
      calc
        _ = ((entries.foldl
              (ReferenceActivePhysicalHorizon.foldRound initial rows selected rewards start hmode)
              next).records.take next.records.length).take acc.records.length := by
          simp [next, List.take_take, Nat.min_eq_left hlen]
        _ = next.records.take acc.records.length := by rw [htail]
        _ = acc.records := by simp [next, ReferenceActivePhysicalHorizon.foldRound]

private theorem foldCalendar_records_take_acc_of_calendar
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (origin intervalStart count : ℕ) (horigin : origin ≤ intervalStart)
    (hspan : intervalStart + count ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial origin)
    (acc : ReferenceActivePhysicalHorizon.Run initial) :
    (ReferenceActivePhysicalHorizon.foldCalendar initial rows selected rewards origin intervalStart
      count horigin hspan hmode acc).records.take acc.records.length = acc.records := by
  exact foldCalendar_records_take_acc initial rows selected rewards origin hmode
    (ReferenceActivePhysicalHorizon.calendarEntries origin intervalStart count horigin hspan) acc

private theorem run_record_input_state_eq_prefix
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (k : ℕ) (hk : k < count) :
    let fullRun := ReferenceActivePhysicalHorizon.run initial rows selected rewards start count
      hspan hmode
    let prefixRun := ReferenceActivePhysicalHorizon.run initial rows selected rewards start k
      (by omega) hmode
    (fullRun.records[k]'(by
      dsimp only [fullRun]
      rw [ReferenceActivePhysicalHorizon.run_record_count]
      exact hk)).input.state = prefixRun.finalState ∧
      prefixRun.records = fullRun.records.take k := by
  dsimp only
  let fullRun := ReferenceActivePhysicalHorizon.run initial rows selected rewards start count hspan hmode
  let prefixRun := ReferenceActivePhysicalHorizon.run initial rows selected rewards start k
    (by omega) hmode
  have hfullCount := ReferenceActivePhysicalHorizon.run_record_count initial rows selected rewards
    start count hspan hmode
  have hkFull : k < fullRun.records.length := by
    simpa [fullRun, hfullCount] using hk
  have hkLe : k ≤ count := by omega
  have hprefixCount := ReferenceActivePhysicalHorizon.run_record_count initial rows selected rewards
    start k (by omega) hmode
  have hsplit0 := ReferenceActivePhysicalHorizon.run_append initial rows selected rewards start k
    (count - k) (by omega) hmode
  have hsplit : fullRun = ReferenceActivePhysicalHorizon.foldCalendar initial rows selected rewards
      start (start + k) (count - k) (by omega) (by omega) hmode prefixRun := by
    dsimp [fullRun, prefixRun] at hsplit0 ⊢
    simpa [Nat.add_sub_of_le hkLe] using hsplit0
  have htakeAcc := foldCalendar_records_take_acc_of_calendar initial rows selected rewards
    start (start + k) (count - k) (by omega) (by omega) hmode prefixRun
  have hprefixRecords : prefixRun.records = fullRun.records.take k := by
    have htake : fullRun.records.take prefixRun.records.length = prefixRun.records := by
      rw [hsplit]
      exact htakeAcc
    have hprefixLen : prefixRun.records.length = k := by
      simpa [prefixRun] using hprefixCount
    simpa [hprefixLen] using htake.symm

  have hkSucc : k + 1 ≤ count := by omega
  let successorRun := ReferenceActivePhysicalHorizon.run initial rows selected rewards start (k + 1)
    (by omega) hmode
  have hsuccessorCount := ReferenceActivePhysicalHorizon.run_record_count initial rows selected rewards
    start (k + 1) (by omega) hmode
  have hsplitSucc0 := ReferenceActivePhysicalHorizon.run_append initial rows selected rewards start
    (k + 1) (count - (k + 1)) (by omega) hmode
  have hsplitSucc : fullRun = ReferenceActivePhysicalHorizon.foldCalendar initial rows selected
      rewards start (start + (k + 1)) (count - (k + 1)) (by omega) (by omega) hmode successorRun := by
    dsimp [fullRun, successorRun] at hsplitSucc0 ⊢
    simpa [Nat.add_sub_of_le hkSucc] using hsplitSucc0
  have htakeSuccAcc := foldCalendar_records_take_acc_of_calendar initial rows selected rewards
    start (start + (k + 1)) (count - (k + 1)) (by omega) (by omega) hmode successorRun
  have hsuccessorRecords : successorRun.records = fullRun.records.take (k + 1) := by
    have htake : fullRun.records.take successorRun.records.length = successorRun.records := by
      rw [hsplitSucc]
      exact htakeSuccAcc
    have hsuccessorLen : successorRun.records.length = k + 1 := by
      simpa [successorRun] using hsuccessorCount
    simpa [hsuccessorLen] using htake.symm

  let entry : ReferenceActivePhysicalHorizon.CalendarEntry p start :=
    ⟨start + k, by omega, by omega⟩
  let input := ReferenceActivePhysicalHorizon.roundInputAt initial rows selected rewards start hmode
    prefixRun entry
  have hstepRun := ReferenceActivePhysicalHorizon.run_successor_step initial rows selected rewards
    start k (by omega) hmode
  have hsuccessorRecordList : successorRun.records = prefixRun.records ++
      [⟨input, ReferenceActivePhysicalStep.step input, rfl⟩] := by
    simpa [successorRun, prefixRun, input, entry,
      ReferenceActivePhysicalHorizon.foldRound,
      ReferenceActivePhysicalHorizon.roundInputAt] using
        congrArg ReferenceActivePhysicalHorizon.Run.records hstepRun
  have hsuccessorIndex : k < successorRun.records.length := by
    rw [hsuccessorCount]
    omega
  let nextRecord : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) :=
    ⟨input, ReferenceActivePhysicalStep.step input, rfl⟩
  have hrecordAtSuccessor? : successorRun.records[k]? = some nextRecord := by
    rw [hsuccessorRecordList]
    have hprefixLen : prefixRun.records.length = k := by
      simpa [prefixRun] using hprefixCount
    simp [nextRecord, hprefixLen]
  have hrecordAtSuccessor : successorRun.records[k]'hsuccessorIndex = nextRecord := by
    simpa [List.getElem?_eq_getElem hsuccessorIndex] using hrecordAtSuccessor?
  have hrecordFull? : fullRun.records[k]? = some nextRecord := by
    calc
      fullRun.records[k]? = (fullRun.records.take (k + 1))[k]? := by simp [hkFull]
      _ = successorRun.records[k]? := by rw [← hsuccessorRecords]
      _ = some nextRecord := hrecordAtSuccessor?
  have hrecordEq : fullRun.records[k]'hkFull =
      nextRecord := by
    simpa [List.getElem?_eq_getElem hkFull] using hrecordFull?
  constructor
  · rw [hrecordEq]
    rfl
  · exact hprefixRecords

private theorem actual_tail_success
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ)
    (ledgerStarted : ReferenceActivePhysicalStep.Ledger rate)
    (htail : ReferenceCoordinatorUpPhysicalCall.tailLedger? prepared payload ledger started
      weights = some ledgerStarted) :
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
  | none => simp [ReferenceCoordinatorUpPhysicalCall.tailLedger?, recordingInput, hrecording] at htail
  | some recording =>
      cases hstart : CoordinatorCollectionLedger.startRound ledger (x.time.val + 1)
          (ReferenceActivePhysicalStep.collectionEnabled ledger x.time)
          (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) with
      | invalid => simp [ReferenceCoordinatorUpPhysicalCall.tailLedger?, recordingInput,
          hrecording, hstart] at htail
      | rejected rejectedLedger =>
          simp [ReferenceCoordinatorUpPhysicalCall.tailLedger?, recordingInput,
            hrecording, hstart] at htail
      | success startedLedger =>
          have heq : startedLedger = ledgerStarted := by
            have hsome : some startedLedger = some ledgerStarted := by
              simpa [ReferenceCoordinatorUpPhysicalCall.tailLedger?, recordingInput,
                hrecording, hstart] using htail
            exact Option.some.inj hsome
          subst startedLedger
          exact ⟨recording, by simpa [recordingInput] using hrecording, hstart⟩

/-- An invalid actual filtered UP reception is absorbed by the physical
collection finish and therefore cannot have an ordinary physical successor. -/
private theorem actual_invalid_up_call_daggers_successor
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (hsite : ReferenceCoordinatorUpPhysicalCall.siteLedger? (x := record.input) = some ledger)
    (hresult : (ReferenceActivePhysicalStep.receiveUp
      (ReferenceActivePhysicalStep.prepare record.input) ledger).result = .invalid) :
    record.output.next.coordinator = .dagger := by
  classical
  let x := record.input
  let prepared := ReferenceActivePhysicalStep.prepare x
  have hresult' : (ReferenceActivePhysicalStep.receiveUp prepared ledger).result = .invalid := by
    simpa [prepared, x] using hresult
  cases hcoord : prepared.coordinator with
  | first outcome =>
      simp [ReferenceCoordinatorUpPhysicalCall.siteLedger?, prepared, x, hcoord] at hsite
  | live registers owned base outcome =>
      cases outcome with
      | cutoffChosen dispatched hstart sourceLedger hinit hledger hdomain hclock hpending
          hnoassignment selected =>
          have hselNe : ReferenceActivePhysicalStep.DispatchCut.selection
              (.live registers owned base
                (.cutoffChosen dispatched hstart sourceLedger hinit hledger hdomain hclock
                  hpending hnoassignment selected)) ≠ none := by
            by_contra hnone
            simp [ReferenceCoordinatorUpPhysicalCall.siteLedger?, prepared, x, hcoord, hnone]
              at hsite
          let payload := registers.payload
          let baseLedger := ReferenceActivePhysicalStep.sharedLedger sourceLedger
          let started := dispatched.startResult
          let weights :=
            (ReferenceActivePhysicalStep.liveRegistersAt registers x.time).complementWeights
          have htail : ReferenceCoordinatorUpPhysicalCall.tailLedger? prepared payload
              baseLedger started weights = some ledger := by
            simpa [ReferenceCoordinatorUpPhysicalCall.siteLedger?, prepared, x, hcoord,
              hselNe, payload, baseLedger, started, weights] using hsite
          obtain ⟨recording, hrecording, hstartRound⟩ :=
            actual_tail_success x prepared payload baseLedger started weights ledger htail
          have hpost := ReferenceActivePhysicalStep.collectionPostChoice_after_start
            prepared payload baseLedger started weights recording ledger hrecording hstartRound
          have hobs : prepared.observeCoordinator =
              ReferenceActivePhysicalStep.collectionPostChoice prepared payload baseLedger started
                weights := by
            have heq := ReferenceActivePhysicalStep.observeCoordinator_live_equation
              prepared registers owned base
              (.cutoffChosen dispatched hstart sourceLedger hinit hledger hdomain hclock
                hpending hnoassignment selected) hcoord
            rw [heq, ite_eq_right hselNe]
          have hnext : record.output.next.coordinator =
              (ReferenceActivePhysicalStep.collectionFinish (x := x) payload started recording
                (ReferenceActivePhysicalStep.receiveUp prepared ledger)).configuration := by
            calc
              _ = (ReferenceActivePhysicalStep.step x).next.coordinator := by rw [record.output_eq]
              _ = prepared.observeCoordinator.configuration :=
                (ReferenceActivePhysicalStep.step_next_fields x).1
              _ = (ReferenceActivePhysicalStep.collectionPostChoice prepared payload baseLedger
                    started weights).configuration :=
                congrArg ReferenceActivePhysicalStep.CoordinatorObservation.configuration hobs
              _ = (ReferenceActivePhysicalStep.collectionFinish (x := x) payload started recording
                    (ReferenceActivePhysicalStep.receiveUp prepared ledger)).configuration :=
                congrArg ReferenceActivePhysicalStep.CoordinatorObservation.configuration hpost
          have hfinish :
              (ReferenceActivePhysicalStep.collectionFinish (x := x) payload started recording
                (ReferenceActivePhysicalStep.receiveUp prepared ledger)).configuration = .dagger := by
            simp only [ReferenceActivePhysicalStep.collectionFinish, hresult',
              ReferenceActivePhysicalStep.coordinatorFailure]
          rw [hnext, hfinish]
      | _ => simp [ReferenceCoordinatorUpPhysicalCall.siteLedger?, prepared, x, hcoord] at hsite
  | collection payload sourceLedger clock cutoff outcome =>
      cases outcome with
      | continuing core snapshot boundary scores =>
          have hselNe : ReferenceActivePhysicalStep.DispatchCut.selection
              (.collection payload sourceLedger clock cutoff
                (.continuing core snapshot boundary scores)) ≠ none := by
            by_contra hnone
            simp [ReferenceCoordinatorUpPhysicalCall.siteLedger?, prepared, x, hcoord, hnone]
              at hsite
          let source := ReferenceActivePhysicalStep.collectionInput x payload sourceLedger clock cutoff
          let weights := CoordinatorCollectionInteractive.PreObservationInputs.weights source
            snapshot.inputsValid.ledger_valid snapshot.inputsValid.assignment_eq
          have htail : ReferenceCoordinatorUpPhysicalCall.tailLedger? prepared payload
              sourceLedger snapshot.clockStarted weights = some ledger := by
            simpa [ReferenceCoordinatorUpPhysicalCall.siteLedger?, prepared, x, hcoord,
              hselNe, source, weights] using hsite
          obtain ⟨recording, hrecording, hstartRound⟩ :=
            actual_tail_success x prepared payload sourceLedger snapshot.clockStarted weights
              ledger htail
          have hpost := ReferenceActivePhysicalStep.collectionPostChoice_after_start
            prepared payload sourceLedger snapshot.clockStarted weights recording ledger
            hrecording hstartRound
          have hobs : prepared.observeCoordinator =
              ReferenceActivePhysicalStep.collectionPostChoice prepared payload
                sourceLedger snapshot.clockStarted weights := by
            have heq := ReferenceActivePhysicalStep.observeCoordinator_collection_equation
              prepared payload sourceLedger clock cutoff
              (.continuing core snapshot boundary scores) hcoord
            rw [heq, ite_eq_right hselNe]
          have hnext : record.output.next.coordinator =
              (ReferenceActivePhysicalStep.collectionFinish (x := x) payload
                snapshot.clockStarted recording
                (ReferenceActivePhysicalStep.receiveUp prepared ledger)).configuration := by
            calc
              _ = (ReferenceActivePhysicalStep.step x).next.coordinator := by rw [record.output_eq]
              _ = prepared.observeCoordinator.configuration :=
                (ReferenceActivePhysicalStep.step_next_fields x).1
              _ = (ReferenceActivePhysicalStep.collectionPostChoice prepared payload
                    sourceLedger snapshot.clockStarted weights).configuration :=
                congrArg ReferenceActivePhysicalStep.CoordinatorObservation.configuration hobs
              _ = (ReferenceActivePhysicalStep.collectionFinish (x := x) payload
                    snapshot.clockStarted recording
                    (ReferenceActivePhysicalStep.receiveUp prepared ledger)).configuration :=
                congrArg ReferenceActivePhysicalStep.CoordinatorObservation.configuration hpost
          have hfinish :
              (ReferenceActivePhysicalStep.collectionFinish (x := x) payload
                snapshot.clockStarted recording
                (ReferenceActivePhysicalStep.receiveUp prepared ledger)).configuration = .dagger := by
            simp only [ReferenceActivePhysicalStep.collectionFinish, hresult',
              ReferenceActivePhysicalStep.coordinatorFailure]
          rw [hnext, hfinish]
      | _ => simp [ReferenceCoordinatorUpPhysicalCall.siteLedger?, prepared, x, hcoord] at hsite
  | invalidCollectionCutoff =>
      simp [ReferenceCoordinatorUpPhysicalCall.siteLedger?, prepared, x, hcoord] at hsite
  | dagger =>
      simp [ReferenceCoordinatorUpPhysicalCall.siteLedger?, prepared, x, hcoord] at hsite

/-- On an actual retained UP call, an ordinary physical successor rules out
the invalid-reception arm of `collectionFinish` and commits the decoder's
whole bank. The selected physical channel is the diagnostic's saved state. -/
theorem record_up_surviving_commit
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (diagnostic : ReferenceActivePhysicalStep.UpDiagnostic p rate)
    (hdiagnostic : record.output.coordinator.up = some diagnostic)
    (hinvariant : ReferenceUpDecoderBankInvariant.upBankInvariant record.input.state)
    (hsurvives : record.output.next.coordinator ≠ .dagger) :
    record.output.next.upDecoderBank = CoordinatorUpReception.decoderBankAfter diagnostic.input ∧
      record.output.next.upDecoderBank diagnostic.input.selectedFollower = diagnostic.decoderAfter := by
  obtain ⟨ledger, hsite, hcheck, hinput, hafter, hcases⟩ :=
    Bandits.Support.ReferenceGeneratedUpBatchCalendar.record_up_physical_commit_cases
      record diagnostic hdiagnostic hinvariant
  have hafter' : diagnostic.decoderAfter =
      (CoordinatorUpReception.decoderTransition diagnostic.input).1 := by
    rw [hinput]
    exact hafter
  rcases hcases with hinvalid | ⟨out, hresult, hbank, hnext⟩
  · have hdagger := actual_invalid_up_call_daggers_successor record ledger hsite hinvalid.1
    exact (hsurvives hdagger).elim
  · refine ⟨hnext.trans hbank, ?_⟩
    calc
      record.output.next.upDecoderBank diagnostic.input.selectedFollower =
          out.2 diagnostic.input.selectedFollower :=
        congrArg (fun bank : CoordinatorUpReception.UpDecoderBank p =>
          bank diagnostic.input.selectedFollower) hnext
      _ = (CoordinatorUpReception.decoderBankAfter diagnostic.input)
          diagnostic.input.selectedFollower := by rw [hbank]
      _ = diagnostic.decoderAfter := by
        simp [CoordinatorUpReception.decoderBankAfter, hafter']

/-- The selected positive quota branch has its actual physical saved bank,
empty pending list, and exact completed-history append after the surviving
physical commit. -/
theorem record_up_surviving_quota_completion
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (diagnostic : ReferenceActivePhysicalStep.UpDiagnostic p rate)
    (hdiagnostic : record.output.coordinator.up = some diagnostic)
    (hinvariant : ReferenceUpDecoderBankInvariant.upBankInvariant record.input.state)
    (hsurvives : record.output.next.coordinator ≠ .dagger)
    (i : Fin (p.m - 1))
    (hselected : diagnostic.input.selectedFollower = i)
    (hpositive : ReferenceGeneratedAffineHashHalf.directionPositive 1 record.input = true)
    (hquota : (record.input.state.upDecoderBank i).pending.length + 1 =
      AffineBatchDecoder.quota p) :
    record.output.next.upDecoderBank i = diagnostic.decoderAfter ∧
      (record.output.next.upDecoderBank i).pending = [] ∧
      (record.output.next.upDecoderBank i).completed =
        (record.input.state.upDecoderBank i).completed ++
          [(record.input.state.upDecoderBank i).pending ++
            [AffineBatchDecoder.entry p
              (ReferenceCoordinatorUpDecoderReplay.constantInputTrace diagnostic.input)
              diagnostic.input.time]] := by
  have hcommit := record_up_surviving_commit record diagnostic hdiagnostic hinvariant hsurvives
  have hselectedCommit : record.output.next.upDecoderBank i = diagnostic.decoderAfter := by
    rw [← hselected]
    exact hcommit.2
  have hquotaCompletion :=
    Bandits.Support.ReferenceGeneratedUpBatchCalendar.record_up_quota_completion
      record diagnostic hdiagnostic i hselected hpositive hquota
  refine ⟨hselectedCommit, ?_, ?_⟩
  · rw [hselectedCommit]
    exact hquotaCompletion.1
  · rw [hselectedCommit, hquotaCompletion.2.1]

theorem generated_up_actual_call_incoming
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T)
    (s : ℕ) (hs : s ≤ t.val) (control0 : TimeControl p)
    (x : ReferenceRetainedBoundaryMeasurability.RetainedLaunchStart
      rate rewards C_star C_h q t s hs control0)
    (control : TimeControl p) (hspan : rate.n ≤ p.T - s) :
    let fields := Bandits.Support.ReferenceGeneratedUpBatchCalendar.retained_launch_start_fields
      rate rewards C_star C_h q t s hs control0 x
    let hstart := (ReferenceInitializationControlRemainder.launchStartRemainderEvent_control_independent
      rate rewards C_star C_h q t s x.1 fields.1 control0 control).mp fields.2
    let source := ReferenceGeneratedActivePrefixFactor.splitSource q t control x.1
    let active := ReferenceGeneratedActivePrefixFactor.generatedActiveSeed
      rate rewards C_star C_h q t control x.1 fields.1 s hs hstart
    let hmode := (ReferenceGeneratedActivePrefixFactor.generatedActiveSeed_spec
      rate rewards C_star C_h q t control x.1 fields.1 s hs hstart).2.1
    let rows := source.1.2
    let selected := ActualInitializationPhysicalStep.selectedRowIndex p source
    let fullRun := ReferenceActivePhysicalHorizon.run active rows selected rewards s rate.n
      (by omega) hmode
    ∀ (k : Fin fullRun.records.length)
      (d : ReferenceActivePhysicalStep.UpDiagnostic p rate),
      let record := fullRun.records[k.val]'k.isLt
      (hd : record.output.coordinator.up = some d) →
      record.input.state =
          (ReferenceActivePhysicalHorizon.run active rows selected rewards s k.val (by
            have hc := ReferenceActivePhysicalHorizon.run_record_count active rows selected rewards
              s rate.n (by omega) hmode
            have hkFull : k.val < fullRun.records.length := k.isLt
            have hc' : fullRun.records.length = rate.n := by
              simpa [fullRun] using hc
            have _hk : k.val < rate.n := Nat.lt_of_lt_of_eq hkFull hc'
            omega) hmode).finalState ∧
        (ReferenceActivePhysicalHorizon.run active rows selected rewards s k.val (by
            have hc := ReferenceActivePhysicalHorizon.run_record_count active rows selected rewards
              s rate.n (by omega) hmode
            have hkFull : k.val < fullRun.records.length := k.isLt
            have hc' : fullRun.records.length = rate.n := by
              simpa [fullRun] using hc
            have _hk : k.val < rate.n := Nat.lt_of_lt_of_eq hkFull hc'
            omega) hmode).records =
          fullRun.records.take k.val ∧
        record.input.rows = rows ∧ record.input.selected = selected ∧
          record.input.rewards = rewards ∧ record.input.time.val = s + k.val ∧
        record.input.state.coordinator ≠ .dagger ∧
        ReferenceUpDecoderBankInvariant.upBankInvariant record.input.state ∧
        (∀ i : Fin (p.m - 1),
          AffineBatchDecoder.collected (record.input.state.upDecoderBank i) =
              ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries
                (fullRun.records.take k.val) i ∧
            (ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries
                (fullRun.records.take k.val) i).length =
              (record.input.state.upDecoderBank i).completed.length * AffineBatchDecoder.quota p +
                (record.input.state.upDecoderBank i).pending.length ∧
            (record.input.state.upDecoderBank i).completed.flatten =
              (ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries
                (fullRun.records.take k.val) i).take
                ((record.input.state.upDecoderBank i).completed.length * AffineBatchDecoder.quota p) ∧
            (record.input.state.upDecoderBank i).pending =
              (ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries
                (fullRun.records.take k.val) i).drop
                ((record.input.state.upDecoderBank i).completed.length * AffineBatchDecoder.quota p)) ∧
        (∃ ledger,
          ReferenceCoordinatorUpPhysicalCall.siteLedger? (x := record.input) = some ledger ∧
          CoordinatorUpReception.receptionInputCheck
            (ReferenceCoordinatorUpPhysicalCall.actualUpInput record.input ledger) = true ∧
          d.input = ReferenceCoordinatorUpPhysicalCall.actualUpInput record.input ledger ∧
          d.decoderAfter = (CoordinatorUpReception.decoderTransition d.input).1 ∧
          d.raw = (CoordinatorUpReception.decoderTransition d.input).2 ∧
          d.parsed = ReferenceUpReception.rawParsedOutput rate d.input ∧
          d.locallyAccepted = ReferenceUpReception.rawParsedLocalAcceptance rate d.input) ∧
        ((∃ ledger,
            (ReferenceActivePhysicalStep.receiveUp
              (ReferenceActivePhysicalStep.prepare record.input) ledger).result = .invalid ∧
            record.output.next.upDecoderBank = record.input.state.upDecoderBank) ∨
          ∃ ledger out,
            ((ReferenceActivePhysicalStep.receiveUp
                (ReferenceActivePhysicalStep.prepare record.input) ledger).result = .success out ∨
              (ReferenceActivePhysicalStep.receiveUp
                (ReferenceActivePhysicalStep.prepare record.input) ledger).result = .rejected out) ∧
            out.2 = CoordinatorUpReception.decoderBankAfter d.input ∧
            record.output.next.upDecoderBank = out.2) ∧
        (record.output.next.coordinator ≠ .dagger →
          record.output.next.upDecoderBank = CoordinatorUpReception.decoderBankAfter d.input ∧
            ∀ i : Fin (p.m - 1),
              d.input.selectedFollower = i →
              ReferenceGeneratedAffineHashHalf.directionPositive 1 record.input = true →
              (record.input.state.upDecoderBank i).pending.length + 1 =
                AffineBatchDecoder.quota p →
              record.output.next.upDecoderBank i = d.decoderAfter ∧
                (record.output.next.upDecoderBank i).pending = [] ∧
                (record.output.next.upDecoderBank i).completed =
                  (record.input.state.upDecoderBank i).completed ++
                    [(record.input.state.upDecoderBank i).pending ++
                      [AffineBatchDecoder.entry p
                        (ReferenceCoordinatorUpDecoderReplay.constantInputTrace d.input)
                        d.input.time]]) := by
  dsimp only
  intro k d hd
  let fields := Bandits.Support.ReferenceGeneratedUpBatchCalendar.retained_launch_start_fields
    rate rewards C_star C_h q t s hs control0 x
  let hstart := (ReferenceInitializationControlRemainder.launchStartRemainderEvent_control_independent
    rate rewards C_star C_h q t s x.1 fields.1 control0 control).mp fields.2
  let source := ReferenceGeneratedActivePrefixFactor.splitSource q t control x.1
  let active := ReferenceGeneratedActivePrefixFactor.generatedActiveSeed
    rate rewards C_star C_h q t control x.1 fields.1 s hs hstart
  let hmode := (ReferenceGeneratedActivePrefixFactor.generatedActiveSeed_spec
    rate rewards C_star C_h q t control x.1 fields.1 s hs hstart).2.1
  let rows := source.1.2
  let selected := ActualInitializationPhysicalStep.selectedRowIndex p source
  let fullRun := ReferenceActivePhysicalHorizon.run active rows selected rewards s rate.n
    (by omega) hmode
  let record := fullRun.records[k.val]'k.isLt
  have hcount := ReferenceActivePhysicalHorizon.run_record_count active rows selected rewards s rate.n
    (by omega) hmode
  have hcount' : fullRun.records.length = rate.n := by simpa [fullRun] using hcount
  have hkFull : k.val < fullRun.records.length := k.isLt
  have hk : k.val < rate.n := Nat.lt_of_lt_of_eq hkFull hcount'
  obtain ⟨hstate, hrecords⟩ := run_record_input_state_eq_prefix active rows selected rewards s rate.n
    (by omega) hmode k.val hk
  have hmem : record ∈ fullRun.records := List.mem_iff_getElem.mpr ⟨k.val, k.isLt, rfl⟩
  obtain ⟨hrows, hselected, hrewards⟩ := ReferenceActivePhysicalHorizon.run_record_inputs
    active rows selected rewards s rate.n (by omega) hmode record hmem
  have htimes := ReferenceActivePhysicalHorizon.run_time_values active rows selected rewards s rate.n
    (by omega) hmode
  have hgetTimes := congrArg (fun times : List ℕ => times[k.val]?) htimes
  have hrecordGet : fullRun.records[k.val]? = some record := by
    simp [record]
  have hrecordTime : (fullRun.records.map fun record => record.input.time.val)[k.val]? =
      some record.input.time.val := by
    simp only [List.getElem?_map, hrecordGet, Option.map_some]
  have hkCalendar : k.val < (ReferenceActivePhysicalHorizon.calendar s rate.n).length := by
    simpa [ReferenceActivePhysicalHorizon.calendar] using hk
  have hcalendar : (ReferenceActivePhysicalHorizon.calendar s rate.n)[k.val] = s + k.val := by
    change (List.range' s rate.n)[k.val] = s + k.val
    exact List.getElem_range'_1 k.val hkCalendar
  have hcalendarTime : (ReferenceActivePhysicalHorizon.calendar s rate.n)[k.val]? =
      some (s + k.val) := by
    rw [List.getElem?_eq_getElem hkCalendar, hcalendar]
  have htime : record.input.time.val = s + k.val := by
    rw [hrecordTime, hcalendarTime] at hgetTimes
    exact Option.some.inj hgetTimes
  obtain ⟨ledger, hsite, hcheck, hinput, hafter, hraw, hparsed, hlocal, _⟩ :=
    Bandits.Support.ReferenceGeneratedUpBatchCalendar.record_up_executed_fields record d hd
  have hordinary : record.input.state.coordinator ≠ .dagger := by
    intro hdagger
    have hsiteNone : ReferenceCoordinatorUpPhysicalCall.siteLedger? (x := record.input) = none := by
      have hprepared : (ReferenceActivePhysicalStep.prepare record.input).coordinator = .dagger := by
        simpa [ReferenceActivePhysicalStep.prepare] using
          ReferenceActivePhysicalStep.dispatch_dagger record.input hdagger
      simp [ReferenceCoordinatorUpPhysicalCall.siteLedger?, hprepared]
    rw [hsiteNone] at hsite
    cases hsite
  have hprefixOrdinary :
      ((ReferenceActivePhysicalHorizon.run active rows selected rewards s k.val (by omega) hmode).finalState).coordinator ≠
        ReferenceActivePhysicalStep.CoordinatorConfiguration.dagger := by
    rw [← hstate]
    exact hordinary
  have hkSpan : k.val ≤ p.T - s := by omega
  have hgeneratedInvariantAndChronology :=
    Bandits.Support.ReferenceGeneratedUpBatchCalendar.generated_up_prefix_bank_chronology
      rate rewards C_star C_h q t s hs control0 x control k.val hkSpan
        ⟨0, by have hm := p.two_le_m; omega⟩
  have hgeneratedInvariant :
      ReferenceUpDecoderBankInvariant.upBankInvariant
        (ReferenceActivePhysicalHorizon.run active rows selected rewards s k.val (by omega) hmode).finalState :=
    hgeneratedInvariantAndChronology.1
  have hrecordInvariant : ReferenceUpDecoderBankInvariant.upBankInvariant record.input.state := by
    rw [hstate]
    exact hgeneratedInvariant
  have hchannels : ∀ i : Fin (p.m - 1),
      AffineBatchDecoder.collected (record.input.state.upDecoderBank i) =
          ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries (fullRun.records.take k.val) i ∧
        (ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries (fullRun.records.take k.val) i).length =
          (record.input.state.upDecoderBank i).completed.length * AffineBatchDecoder.quota p +
            (record.input.state.upDecoderBank i).pending.length ∧
        (record.input.state.upDecoderBank i).completed.flatten =
          (ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries (fullRun.records.take k.val) i).take
            ((record.input.state.upDecoderBank i).completed.length * AffineBatchDecoder.quota p) ∧
        (record.input.state.upDecoderBank i).pending =
          (ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries (fullRun.records.take k.val) i).drop
            ((record.input.state.upDecoderBank i).completed.length * AffineBatchDecoder.quota p) := by
    intro i
    have hi := Bandits.Support.ReferenceGeneratedUpBatchCalendar.generated_up_prefix_bank_chronology
      rate rewards C_star C_h q t s hs control0 x control k.val (by omega) i
    have hbank := hi.2 hprefixOrdinary
    rw [← hstate] at hbank
    rw [hrecords] at hbank
    exact hbank
  have hcommit := Bandits.Support.ReferenceGeneratedUpBatchCalendar.record_up_physical_commit_cases
    record d hd hrecordInvariant
  refine ⟨hstate, hrecords, hrows, hselected, hrewards, htime, hordinary,
    hrecordInvariant, hchannels, ?_, ?_, ?_⟩
  · exact ⟨ledger, hsite, hcheck, hinput, hafter, hraw, hparsed, hlocal⟩
  · obtain ⟨commitLedger, hsiteCommit, hcheckCommit, hinputCommit, hafterCommit, hcases⟩ := hcommit
    rcases hcases with hinvalid | ⟨out, hresult, hbank, hnext⟩
    · exact Or.inl ⟨commitLedger, hinvalid.1, hinvalid.2⟩
    · exact Or.inr ⟨commitLedger, out, hresult, hbank, hnext⟩
  · intro hsurvives
    have hsurvivingCommit := record_up_surviving_commit record d hd hrecordInvariant hsurvives
    refine ⟨hsurvivingCommit.1, ?_⟩
    intro i hselectedDiagnostic hpositive hquota
    exact record_up_surviving_quota_completion record d hd hrecordInvariant hsurvives
      i hselectedDiagnostic hpositive hquota

end Bandits.Support.ReferenceGeneratedUpCallBankReplay

end
