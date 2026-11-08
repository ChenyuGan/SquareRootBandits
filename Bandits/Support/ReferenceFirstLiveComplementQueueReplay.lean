/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLiveCoordinatorNumericalService

import Lean.Elab.Tactic.Omega
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.TakeWhile

/-!
# Source-cell join for the actual first-live complement queue

Sources: `sources/zip4/manuscript/04_slow_fast_learner.tex:140-174`,
`sources/zip4/manuscript/05_binary_transport.tex:354-396`,
`sources/zip4/manuscript/06_interruptions.tex:246-295,391-408`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-64`.

The result joins the checked zero-seeded diagnostic replay on the original
first-live physical prefix to the actual whole numerical source cells. Each
calendar round is retained, including enabled rounds with zero arrivals. It
stops at the first chosen cutoff and makes no global queue or regret claim.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceFirstWindowNumericalStream
open Bandits.Support.ReferenceFirstLiveConfirmationHistory
open Bandits.Support.ReferenceFirstComplementReplay
open Bandits.Support.ReferenceAssignmentPayloadChronology
open Bandits.Support.ReferenceAssignmentPayloadPersistence
open Bandits.Support.ReferenceSelectedPayloadChronology
open Bandits.Support.CoordinatorLiveChoiceRecorderStep
open Bandits.Support.CoordinatorLiveServiceFinish
open Bandits.Support.CoordinatorCollectionLedger
open Bandits.Support.CollectionKnownQueueContinuation
open Bandits.Support.CanonicalFastSampling

namespace Bandits.Support.ReferenceFirstLiveComplementQueueReplay

variable {p : ConstructorDimensions.Parameters}

private theorem servicePass_recording_eq
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (recording : CoordinatorRecordingOperation.Output p)
    (serviced : CoordinatorLiveServiceFinish.ServicedRegisters r q)
    (hservice : CoordinatorLiveServiceFinish.servicePass r q recording = .ok serviced) :
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
        result.map (fun output => output.recording)) hservice
  rw [hmap, hservice] at hmapped
  exact (Except.ok.inj hmapped).symm

private theorem diagnostic_arrival_eq_serviced
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (payload : AssignmentStartPayload.Input p rate.eta)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (recording : CoordinatorRecordingOperation.Output p)
    (serviced : CoordinatorLiveServiceFinish.ServicedRegisters r q)
    (hservice : CoordinatorLiveServiceFinish.servicePass r q recording = .ok serviced)
    (hrecording : record.output.coordinator.recording = some recording)
    (hpayload : r.payload = payload)
    (a : FastArm payload.slowSet) :
    CoordinatorCollectionLedger.localArrival
        (ReferenceCollectionRawBufferHistory.rawDiagnostic record) a.1 =
      serviced.arrival ⟨a.1, by simpa [hpayload] using a.2⟩ := by
  let a' : FastArm r.payload.slowSet := ⟨a.1, by simpa [hpayload] using a.2⟩
  have hservicedRecording := servicePass_recording_eq r q recording serviced hservice
  have harrival := serviced.arrival_eq a'
  change CoordinatorCollectionLedger.localArrival
      (ReferenceCollectionRawBufferHistory.rawDiagnostic record) a.1 = serviced.arrival a'
  rw [harrival, hservicedRecording]
  cases hgate : recording.gateArm with
  | none =>
      simp [ReferenceCollectionRawBufferHistory.rawDiagnostic, hrecording, hgate,
        CoordinatorCollectionLedger.localArrival, CoordinatorLiveServiceFinish.complementArrival]
  | some arm =>
      by_cases hsame : arm = a.1
      · subst arm
        simp [ReferenceCollectionRawBufferHistory.rawDiagnostic, hrecording, hgate,
          CoordinatorCollectionLedger.localArrival, CoordinatorLiveServiceFinish.complementArrival, a']
      · have hsame' : arm ≠ a'.1 := by simpa [a'] using hsame
        simp [ReferenceCollectionRawBufferHistory.rawDiagnostic, hrecording, hgate,
          CoordinatorCollectionLedger.localArrival, CoordinatorLiveServiceFinish.complementArrival,
          hsame, hsame', a']

private theorem current_live_diagnostic_cell_join
    (rate : ReferenceFirstWindowNumericalStream.RateInput p)
    (source : ReferenceFirstWindowNumericalStream.SourceInput p)
    (rewards : ReferenceFirstWindowNumericalStream.RewardTable p)
    (C_star C_h : ℝ)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (count : ℕ)
    (hspan : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed +
          count ≤ p.T)
    (k : Fin (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
      rate source rewards C_star C_h hc count hspan).length)
    (payload : AssignmentStartPayload.Input p rate.eta)
    (hselected : (ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
      rate source rewards C_star C_h hc count hspan k).selected.view.payload = payload)
    (a : FastArm payload.slowSet)
    (henabled : (ReferenceFirstComplementReplay.liveDiagnosticQueueRecord payload a.1
      ((ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
        rate source rewards C_star C_h hc count hspan)[k.val])).1 = true) :
    ReferenceFirstComplementReplay.liveDiagnosticQueueRecord payload a.1
        ((ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
          rate source rewards C_star C_h hc count hspan)[k.val]) =
      ( (ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
          rate source rewards C_star C_h hc count hspan k).input.enabled,
        RecordedQueueRun.quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate)
          (ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
            rate source rewards C_star C_h hc count hspan k).input a.1 ) ∧
    (ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
      rate source rewards C_star C_h hc count hspan k).input.enabled = true := by
  let record := (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
    rate source rewards C_star C_h hc count hspan)[k.val]
  let cell := ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
    rate source rewards C_star C_h hc count hspan k
  have hbranches :=
    ReferenceFirstLiveCoordinatorNumericalService.actual_first_live_coordinator_service_branches
      rate source rewards C_star C_h hc count hspan k
  have hnumerical :=
    ReferenceFirstLiveCoordinatorNumericalService.actual_first_live_coordinator_numerical_service
      rate source rewards C_star C_h hc count hspan k
  dsimp only at hnumerical
  have hcellEnabled : cell.input.enabled = true := by
    have hfacts := ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt_facts
      rate source rewards C_star C_h hc count hspan k
    simpa [record, cell] using hfacts.2.2.2.2.1
  rcases hbranches with hfirst | hcontinuing
  · rcases hfirst with ⟨installed, selected, hbranch, htime⟩
    rw [hbranch] at hnumerical
    rcases hnumerical with ⟨recording, serviced, pending, finished,
      _hrun, hrecording, hservice, hbranchPayload, _hcellEnabled,
      harrival, _hserviceFields, _hdomain, _hzero, _hconfirmation, _hfinish,
      _hfinishedPending, _hfailure, _hup, _hbank, _hnext⟩
    have hpayload : installed.registers.payload = payload := hbranchPayload.trans hselected
    let a' : FastArm installed.registers.payload.slowSet :=
      ⟨a.1, by simpa [hpayload] using a.2⟩
    have hdiag := diagnostic_arrival_eq_serviced record payload installed.registers
      installed.ownedRegisters recording serviced hservice hrecording hpayload a
    have harr := harrival a'
    have hpair :
        (ReferenceFirstComplementReplay.liveDiagnosticQueueRecord payload a.1 record).1 =
            cell.input.enabled ∧
          (ReferenceFirstComplementReplay.liveDiagnosticQueueRecord payload a.1 record).2 =
            RecordedQueueRun.quantizedArrival
              (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell.input a.1 := by
      constructor
      · rw [hcellEnabled]
        exact henabled
      · calc
          (ReferenceFirstComplementReplay.liveDiagnosticQueueRecord payload a.1 record).2 =
              CoordinatorCollectionLedger.localArrival
                (ReferenceCollectionRawBufferHistory.rawDiagnostic record) a.1 := rfl
          _ = serviced.arrival a' := by simpa [a'] using hdiag
          _ = RecordedQueueRun.quantizedArrival
                (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell.input a.1 := by
              simpa [a'] using harr
    constructor
    · exact Prod.ext hpair.1 hpair.2
    · exact hcellEnabled
  · rcases hcontinuing with
      ⟨registers, owned, base, dispatched, hstart, continuation, selected, hbranch⟩
    rw [hbranch] at hnumerical
    rcases hnumerical with ⟨recording, serviced, pending, finished,
      _hrun, hrecording, hservice, hbranchPayload, _hcellEnabled,
      harrival, _hserviceFields, _hdomain, _hzero, _hconfirmation, _hfinish,
      _hfinishedPending, _hfailure, _hup, _hbank, _hnext⟩
    have hpayload : registers.payload = payload := hbranchPayload.trans hselected
    let actualRegisters := ReferenceActivePhysicalStep.liveRegistersAt registers record.input.time
    let actualOwned := ReferenceActivePhysicalStep.liveOwnedAt registers owned record.input.time
    have hpayloadActual : actualRegisters.payload = payload := hpayload
    let a' : FastArm actualRegisters.payload.slowSet :=
      ⟨a.1, by simpa [hpayloadActual] using a.2⟩
    have hdiag := diagnostic_arrival_eq_serviced record payload actualRegisters actualOwned recording
      serviced hservice hrecording hpayloadActual a
    have harr := harrival a'
    have hpair :
        (ReferenceFirstComplementReplay.liveDiagnosticQueueRecord payload a.1 record).1 =
            cell.input.enabled ∧
          (ReferenceFirstComplementReplay.liveDiagnosticQueueRecord payload a.1 record).2 =
            RecordedQueueRun.quantizedArrival
              (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell.input a.1 := by
      constructor
      · rw [hcellEnabled]
        exact henabled
      · calc
          (ReferenceFirstComplementReplay.liveDiagnosticQueueRecord payload a.1 record).2 =
              CoordinatorCollectionLedger.localArrival
                (ReferenceCollectionRawBufferHistory.rawDiagnostic record) a.1 := rfl
          _ = serviced.arrival a' := by simpa [a'] using hdiag
          _ = RecordedQueueRun.quantizedArrival
                (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell.input a.1 := by
              simpa [a'] using harr
    constructor
    · exact Prod.ext hpair.1 hpair.2
    · exact hcellEnabled

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

private theorem actual_first_live_window_length_le_count
    (rate : ReferenceFirstWindowNumericalStream.RateInput p)
    (source : ReferenceFirstWindowNumericalStream.SourceInput p)
    (rewards : ReferenceFirstWindowNumericalStream.RewardTable p)
    (C_star C_h : ℝ)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (count : ℕ)
    (hspan : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed +
          count ≤ p.T) :
    (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
      rate source rewards C_star C_h hc count hspan).length ≤ count := by
  calc
    (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
      rate source rewards C_star C_h hc count hspan).length ≤
        (ReferenceFirstWindowNumericalStream.actualFirstLiveRun
          rate source rewards C_star C_h hc count hspan).records.length :=
      (List.takeWhile_prefix _).length_le
    _ = count := by
      simpa [ReferenceFirstWindowNumericalStream.actualFirstLiveRun] using
        ReferenceActivePhysicalHorizon.run_record_count
          (ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hc)
          source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
          (ReferenceInitializationRun.elapsed p
            (ReferenceInitializationRun.output
              (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed)
          count hspan
          (ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
            rate source rewards C_star C_h hc).activeAtStart

/-- The actual first-live prefix joins the original source-cell arrivals to
the checked diagnostic replay on every coordinator-complement arm. It stops
before the first chosen cutoff round. -/
theorem actual_first_live_complement_prefix_replay
    (rate : ReferenceFirstWindowNumericalStream.RateInput p)
    (source : ReferenceFirstWindowNumericalStream.SourceInput p)
    (rewards : ReferenceFirstWindowNumericalStream.RewardTable p)
    (C_star C_h : ℝ)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (count : ℕ)
    (hspan : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed +
          count ≤ p.T)
    (b : ℕ)
    (hb : b ≤ (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
      rate source rewards C_star C_h hc count hspan).length) :
    let s := ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
    let I := ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hc
    let seed := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
      rate source rewards C_star C_h hc
    let E := ReferenceFirstWindowNumericalStream.actualFirstLiveRun
      rate source rewards C_star C_h hc count hspan
    let Wlive := ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
      rate source rewards C_star C_h hc count hspan
    let cells := ReferenceFirstWindowNumericalStream.actualLiveSourceCells
      rate source rewards C_star C_h hc count hspan
    s + b ≤ p.T ∧
    (b = 0 →
      (ReferenceActivePhysicalHorizon.run I source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s b
        (by
          have hwindowCount := actual_first_live_window_length_le_count
            rate source rewards C_star C_h hc count hspan
          omega) seed.activeAtStart).finalState = I ∧
      (ReferenceActivePhysicalHorizon.run I source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s b
        (by
          have hwindowCount := actual_first_live_window_length_le_count
            rate source rewards C_star C_h hc count hspan
          omega) seed.activeAtStart).finalState.coordinator = .first) ∧
    (0 < b →
      ∃ r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta,
        ∃ owned : CoordinatorLiveServiceFinish.OwnedRegisters r,
          ∃ base : Fin (p.m - 1) → ℕ,
            (ReferenceActivePhysicalHorizon.run I source.1.2
              (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s b
              (by
                have hwindowCount := actual_first_live_window_length_le_count
                  rate source rewards C_star C_h hc count hspan
                omega) seed.activeAtStart).finalState.coordinator = .live r owned base ∧
            s + b ≤ p.T ∧
            r.payload.sigma.val = s ∧
            r.payload.n = rate.n ∧
            (∀ i, base i = 0) ∧
            (∃ birth : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate),
              birth ∈ (ReferenceActivePhysicalHorizon.run I source.1.2
                (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s b
                (by
                  have hwindowCount := actual_first_live_window_length_le_count
                    rate source rewards C_star C_h hc count hspan
                  omega) seed.activeAtStart).records ∧
              ReferenceAssignmentPayloadPersistence.InstallationBirth birth r.payload ∧
              birth.input.time.val = s ∧
              (∃ installed selected,
                birth.output.preparation.coordinator = .first (.chosen installed selected) ∧
                installed.registers.payload = r.payload)) ∧
            (∀ a : FastArm r.payload.slowSet,
              let Da := fun v => (cells.take v).map fun c =>
                (c.enabled, RecordedQueueRun.quantizedArrival
                  (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a.1)
              let Va := fun v => QueueReplay.replay (4 * rate.n) (0, 0) (Da v)
              ReferenceFirstComplementReplay.liveDiagnosticQueueRecords r.payload a.1 Wlive b = Da b ∧
              (∀ d ∈ ReferenceFirstComplementReplay.liveDiagnosticQueueRecords
                r.payload a.1 Wlive b, d.1 = true) ∧
              (r.complementScores a, owned.queue a) = Va b ∧
              owned.previousService a = (Va b).1 - (Va (b - 1)).1 ∧
              r.complementScores a ≤ p.T * D p ∧ owned.queue a ≤ p.T * D p ∧
              owned.previousService a ≤ D p ∧
              (∀ k : Fin b,
                let k' : Fin (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
                  rate source rewards C_star C_h hc count hspan).length :=
                    ⟨k.val, by omega⟩
                let record := (Wlive[k.val])
                let cell := ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
                  rate source rewards C_star C_h hc count hspan k'
                ReferenceFirstComplementReplay.liveDiagnosticQueueRecord r.payload a.1 record =
                    (cell.input.enabled, RecordedQueueRun.quantizedArrival
                      (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell.input a.1) ∧
                  cell.input.enabled = true))) := by
  classical
  dsimp only
  let start := ReferenceInitializationRun.elapsed p
    (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
  let initial := ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hc
  let seed := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
    rate source rewards C_star C_h hc
  let run := ReferenceFirstWindowNumericalStream.actualFirstLiveRun
    rate source rewards C_star C_h hc count hspan
  let window := ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
    rate source rewards C_star C_h hc count hspan
  let cells := ReferenceFirstWindowNumericalStream.actualLiveSourceCells
    rate source rewards C_star C_h hc count hspan
  let rows := source.1.2
  let selectedRow := ActualInitializationPhysicalStep.selectedRowIndex p source
  have hrun : run = ReferenceActivePhysicalHorizon.run initial rows selectedRow rewards
      start count hspan seed.activeAtStart := rfl
  have hwindow : window = ReferenceFirstLiveConfirmationHistory.firstLiveWindow run.records := rfl
  have hwindowCount : window.length ≤ count := by
    simpa [window, run] using actual_first_live_window_length_le_count
      rate source rewards C_star C_h hc count hspan
  have hcellsLength : cells.length = window.length := by
    change (ReferenceFirstWindowNumericalStream.actualLiveSourceCells
        rate source rewards C_star C_h hc count hspan).length =
      (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
        rate source rewards C_star C_h hc count hspan).length
    exact ReferenceFirstWindowNumericalStream.actualLiveSourceCells_length
      rate source rewards C_star C_h hc count hspan
  have hbcount : b ≤ count := hb.trans hwindowCount
  have hspanB : start + b ≤ p.T := by omega
  have hsafety := ReferenceFirstLiveCoordinatorSafety.run_first_live_coordinator_safety
    initial rows selectedRow rewards start count hspan seed.activeAtStart seed.coordinatorFirst
  have hzero : (ReferenceActivePhysicalHorizon.run initial rows selectedRow rewards
      start 0 (by omega) seed.activeAtStart).finalState = initial :=
    ReferenceActivePhysicalHorizon.run_zero_final initial rows selectedRow rewards start
      (by omega) seed.activeAtStart
  refine ⟨hspanB, ?_, ?_⟩
  · intro hbzero
    subst b
    exact ⟨hzero, by rw [hzero]; exact seed.coordinatorFirst⟩
  · intro hbpos
    obtain ⟨r, owned, base, hlive⟩ := (hsafety.2.1 b hb).2 hbpos
    obtain ⟨hpositive, hsigma, hbase, hbirth, hproposal, hreplay⟩ :=
      ReferenceFirstComplementReplay.run_first_complement_replay
        initial rows selectedRow rewards start count hspan seed.activeAtStart
        seed.coordinatorFirst b hbcount hb r owned base hlive
    have hn : r.payload.n = rate.n := ReferenceActivePhysicalStep.payload_n_eq r.payload
    have hfinalPrefix : ReferenceActivePhysicalHorizon.run initial rows selectedRow rewards
        start b (by omega) seed.activeAtStart =
      ReferenceActivePhysicalHorizon.run initial rows selectedRow rewards
        start b (by omega) seed.activeAtStart := rfl
    have prefix_mem : ∀ n (hn : n ≤ count)
        (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)),
        record ∈ (ReferenceActivePhysicalHorizon.run initial rows selectedRow rewards
          start n (by omega) seed.activeAtStart).records → record ∈ run.records := by
      intro n hn record hrecord
      obtain ⟨suffix, hrecords⟩ := ReferenceCollectionPhaseHistory.run_records_prefix
        initial rows selectedRow rewards start n (count - n) (by omega) seed.activeAtStart
      have hrecords' : run.records =
          (ReferenceActivePhysicalHorizon.run initial rows selectedRow rewards
            start n (by omega) seed.activeAtStart).records ++ suffix := by
        rw [hrun]
        simpa only [Nat.add_sub_of_le hn] using hrecords
      rw [hrecords']
      exact List.mem_append_left _ hrecord
    rcases hbirth with ⟨birth, hbirthPrefix, hborn, hbirthTime, hfirstBirth⟩
    have hbirthRun : birth ∈ run.records := prefix_mem b hbcount birth hbirthPrefix
    have hwindowPrefix : window.IsPrefix run.records := by
      rw [hwindow]
      exact List.takeWhile_prefix _
    have payload_at : ∀ k : Fin b,
        (ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
          rate source rewards C_star C_h hc count hspan
          ⟨k.val, lt_of_lt_of_le k.isLt hb⟩).selected.view.payload = r.payload := by
      intro k
      let record := window[k.val]
      have hkWindow : k.val < window.length := lt_of_lt_of_le k.isLt hb
      let kWindow : Fin window.length := ⟨k.val, hkWindow⟩
      let cell := ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
        rate source rewards C_star C_h hc count hspan kWindow
      have hrecordMem : record ∈ run.records := by
        change window[k.val] ∈ run.records
        rw [hwindowPrefix.getElem hkWindow]
        exact List.getElem_mem (lt_of_lt_of_le hkWindow hwindowPrefix.length_le)
      have hkRun : k.val < run.records.length :=
        lt_of_lt_of_le hkWindow hwindowPrefix.length_le
      obtain ⟨prefixLength, hprefixLength, hrecordTime, hrecordState⟩ :=
        ReferenceSelectedPayloadChronology.actualRunRecord_has_prefix
          initial rows selectedRow rewards start count hspan seed.activeAtStart record hrecordMem
      have htimes := ReferenceActivePhysicalHorizon.run_time_values initial rows selectedRow
        rewards start count hspan seed.activeAtStart
      have hrecordTime' : record.input.time.val = start + k.val := by
        have hkWindow : k.val < window.length := lt_of_lt_of_le k.isLt hb
        have hprefixElem := hwindowPrefix.getElem hkWindow
        have hmapBound : k.val <
            (run.records.map (fun current => current.input.time.val)).length := by
          simpa using hkRun
        have hmapEq : run.records.map (fun current => current.input.time.val) =
            ReferenceActivePhysicalHorizon.calendar start count := by
          simpa [hrun] using htimes
        have hcalendarBound : k.val <
            (ReferenceActivePhysicalHorizon.calendar start count).length := by
          simpa [ReferenceActivePhysicalHorizon.calendar] using
            (show k.val < count from lt_of_lt_of_le k.isLt hbcount)
        calc
          record.input.time.val = run.records[k.val].input.time.val := by
            change window[k.val].input.time.val = _
            rw [hprefixElem]
          _ = (run.records.map (fun current => current.input.time.val))[k.val] := by
            simp [hmapBound]
          _ = (ReferenceActivePhysicalHorizon.calendar start count)[k.val] :=
            List.getElem_of_eq hmapEq hmapBound
          _ = start + k.val := by
            simp [ReferenceActivePhysicalHorizon.calendar, hcalendarBound]
      have hprefixEq : prefixLength = k.val := by omega
      have hrecordState' : record.input.state =
          (ReferenceActivePhysicalHorizon.run initial rows selectedRow rewards
            start k.val (by omega) seed.activeAtStart).finalState := by
        simpa [hprefixEq] using hrecordState
      have hlocal := ReferenceSelectedPayloadChronology.actualSelectedPayload_local_stored_or_birth
        record cell.selected cell.selection_actual
      by_cases hkzero : k.val = 0
      · have hstateInitial : record.input.state = initial := by
          rw [hrecordState']
          simpa only [hkzero] using
            ReferenceActivePhysicalHorizon.run_zero_final initial rows selectedRow rewards
              start (by omega) seed.activeAtStart
        have hlocal' : InstallationBirth record cell.selected.view.payload := by
          rcases hlocal with hstored | hbornCurrent
          · rw [hstateInitial, seed.coordinatorFirst,
              ReferenceAssignmentPayloadPersistence.storedPayload_first] at hstored
            cases hstored
          · exact hbornCurrent
        have hselectedTime := ReferenceAssignmentPayloadChronology.installationBirth_time_eq
          record cell.selected.view.payload hlocal'
        have hbirthEq : record = birth :=
          ReferenceAssignmentPayloadChronology.run_records_time_injective
            initial rows selectedRow rewards start count hspan seed.activeAtStart
            hrecordMem hbirthRun (by rw [hrecordTime', hkzero, hbirthTime]; simp)
        rw [hbirthEq] at hlocal'
        exact ReferenceAssignmentPayloadChronology.installationBirth_payload_unique
          birth cell.selected.view.payload r.payload hlocal' hborn
      · have hkpos : 0 < k.val := Nat.pos_of_ne_zero hkzero
        have hkSafety : k.val ≤ window.length := Nat.le_trans (Nat.le_of_lt k.isLt) hb
        have hkCount : k.val ≤ count := Nat.le_trans (Nat.le_of_lt k.isLt) hbcount
        obtain ⟨rCurrent, ownedCurrent, baseCurrent, hliveCurrent⟩ :=
          (hsafety.2.1 k.val hkSafety).2 hkpos
        obtain ⟨_, _, _, hbirthCurrent, _, _⟩ :=
          ReferenceFirstComplementReplay.run_first_complement_replay
            initial rows selectedRow rewards start count hspan seed.activeAtStart
            seed.coordinatorFirst k.val hkCount hkSafety
            rCurrent ownedCurrent baseCurrent hliveCurrent
        rcases hbirthCurrent with ⟨birthCurrent, hbirthCurrentPrefix, hbornCurrent,
          hbirthCurrentTime, _⟩
        have hbirthCurrentRun : birthCurrent ∈ run.records :=
          prefix_mem k.val hkCount birthCurrent hbirthCurrentPrefix
        have hstateLive : record.input.state.coordinator = .live rCurrent ownedCurrent baseCurrent := by
          rw [hrecordState', hliveCurrent]
        have hbranches :=
          ReferenceFirstLiveCoordinatorNumericalService.actual_first_live_coordinator_service_branches
            rate source rewards C_star C_h hc count hspan kWindow
        have hprep : record.output.preparation = ReferenceActivePhysicalStep.prepare record.input := by
          rw [record.output_eq]
          rfl
        have hprepCoord := congrArg ReferenceActivePhysicalStep.PreparedRound.coordinator hprep
        have hliveBranch : ∃ registers owned base dispatched hstart continuation selected,
            record.output.preparation.coordinator =
              .live registers owned base (.continuingChosen dispatched hstart continuation selected) := by
          rcases hbranches with hfirst | hcontinuing
          · rcases hfirst with ⟨installed, selected, hbranch, _⟩
            have hfalse : False := by
              have hprepDispatch : record.output.preparation.coordinator =
                  ReferenceActivePhysicalStep.dispatch record.input := by
                calc
                  record.output.preparation.coordinator =
                      (ReferenceActivePhysicalStep.prepare record.input).coordinator := hprepCoord
                  _ = ReferenceActivePhysicalStep.dispatch record.input := rfl
              rw [hbranch] at hprepDispatch
              unfold ReferenceActivePhysicalStep.dispatch at hprepDispatch
              rw [hstateLive] at hprepDispatch
              cases hprepDispatch
            exact False.elim hfalse
          · rcases hcontinuing with ⟨registers, owned, base, dispatched,
              hstart, continuation, selected, hbranch⟩
            exact ⟨registers, owned, base, dispatched, hstart, continuation, selected, hbranch⟩
        obtain ⟨registers, ownedNow, baseNow, dispatched, hstart, continuation,
          selectedNow, hbranch⟩ := hliveBranch
        have hselectedCurrent : cell.selected.view.payload = rCurrent.payload := by
          rcases hlocal with hstored | hbornCurrentSelection
          · rw [hrecordState', hliveCurrent,
              ReferenceAssignmentPayloadPersistence.storedPayload_live] at hstored
            exact Option.some.inj hstored.symm
          · have hfalse : False := by
              simp [ReferenceAssignmentPayloadPersistence.InstallationBirth, hbranch]
                at hbornCurrentSelection
            exact False.elim hfalse
        have hbirthCurrentEq : birthCurrent = birth :=
          ReferenceAssignmentPayloadChronology.run_records_time_injective
            initial rows selectedRow rewards start count hspan seed.activeAtStart
            hbirthCurrentRun hbirthRun (by rw [hbirthCurrentTime, hbirthTime])
        have hbornAtCurrent : InstallationBirth birthCurrent r.payload := by
          rw [hbirthCurrentEq]
          exact hborn
        have hcurrentPayloadEq :=
          ReferenceAssignmentPayloadChronology.installationBirth_payload_unique birthCurrent
            rCurrent.payload r.payload hbornCurrent hbornAtCurrent
        exact hselectedCurrent.trans hcurrentPayloadEq
    have hscale := ReferenceActivePhysicalStep.payload_n_eq r.payload
    have hwindowLength := hwindowCount
    have hstateLength : (ReferenceActivePhysicalHorizon.run initial rows selectedRow rewards
        start b (by omega) seed.activeAtStart).finalState.coordinator = .live r owned base := hlive
    refine ⟨r, owned, base, ?_, ?_, hsigma, hscale, hbase, ?_, ?_⟩
    · simpa [initial, start] using hlive
    · exact hspanB
    · refine ⟨birth, ?_, hborn, hbirthTime, ?_⟩
      · exact hbirthPrefix
      · exact hfirstBirth
    · intro a
      have hbWindow : b ≤ window.length := by simpa [window] using hb
      let Da := fun v => (cells.take v).map fun c =>
        (c.enabled, RecordedQueueRun.quantizedArrival
          (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a.1)
      let Va := fun v => QueueReplay.replay (4 * rate.n) (0, 0) (Da v)
      have hreplayA := hreplay a
      dsimp only at hreplayA
      rcases hreplayA with ⟨hDlen, hDenabled, hregisters, hprevious⟩
      have hDlenWindow :
          (ReferenceFirstComplementReplay.liveDiagnosticQueueRecords r.payload a.1 window b).length = b := by
        simpa [window, run, hwindow, hrun] using hDlen
      have hDenabledWindow : ∀ d ∈
          ReferenceFirstComplementReplay.liveDiagnosticQueueRecords r.payload a.1 window b,
          d.1 = true := by
        simpa [window, run, hwindow, hrun] using hDenabled
      have hregistersWindow : (r.complementScores a, owned.queue a) =
          QueueReplay.replay (4 * rate.n) (0, 0)
            (ReferenceFirstComplementReplay.liveDiagnosticQueueRecords r.payload a.1 window b) := by
        simpa [window, run, hwindow, hrun, hscale] using hregisters
      have hpreviousWindow : owned.previousService a =
          CollectionKnownQueueContinuation.replayLastService (4 * rate.n) (0, 0) 0
            (ReferenceFirstComplementReplay.liveDiagnosticQueueRecords r.payload a.1 window b) := by
        simpa [window, run, hwindow, hrun, hscale] using hprevious
      have hrecords :
          ReferenceFirstComplementReplay.liveDiagnosticQueueRecords r.payload a.1 window b = Da b := by
        apply List.ext_getElem
        · simp [ReferenceFirstComplementReplay.liveDiagnosticQueueRecords, Da,
            Nat.min_eq_left hb, hcellsLength, Nat.min_eq_left hb]
        · intro i hleft hright
          have hi : i < b := by simpa [hDlenWindow] using hleft
          have hiWindow : i < window.length := lt_of_lt_of_le hi hbWindow
          let k : Fin b := ⟨i, hi⟩
          let k' : Fin window.length := ⟨i, hiWindow⟩
          let cell := ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
            rate source rewards C_star C_h hc count hspan k'
          have hinput := ReferenceFirstWindowNumericalStream.actualLiveSourceCells_get
            rate source rewards C_star C_h hc count hspan k'
          have hdiagMem :
              ReferenceFirstComplementReplay.liveDiagnosticQueueRecord r.payload a.1 window[i] ∈
                ReferenceFirstComplementReplay.liveDiagnosticQueueRecords r.payload a.1 window b :=
            List.mem_map.mpr ⟨window[i], by
              have htakenBound : i < (window.take b).length := by
                simpa [List.length_take, Nat.min_eq_left hbWindow] using hi
              have htakenMem : (window.take b)[i] ∈ window.take b :=
                List.getElem_mem htakenBound
              have htakenElem : (window.take b)[i] = window[i] := by
                simp [List.getElem_take, hi]
              rw [← htakenElem]
              exact htakenMem, rfl⟩
          have hdiagEnabled := hDenabledWindow _ hdiagMem
          have hjoin := current_live_diagnostic_cell_join rate source rewards C_star C_h
            hc count hspan k' r.payload (payload_at k) a hdiagEnabled
          have hleftGet :
              (ReferenceFirstComplementReplay.liveDiagnosticQueueRecords r.payload a.1 window b)[i] =
                ReferenceFirstComplementReplay.liveDiagnosticQueueRecord r.payload a.1 window[i] := by
            simp [ReferenceFirstComplementReplay.liveDiagnosticQueueRecords,
              List.getElem_map, List.getElem_take, Nat.min_eq_left hb, hi]
          have hrightGet : (Da b)[i] =
              (cell.input.enabled, RecordedQueueRun.quantizedArrival
                (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell.input a.1) := by
            simp only [Da, List.getElem_map, List.getElem_take, Nat.min_eq_left hb, hi]
            rw [hinput]
          rw [hleftGet, hrightGet]
          exact hjoin.1
      have hstateReplay : (r.complementScores a, owned.queue a) = Va b := by
        simpa [Va, Da, hrecords] using hregistersWindow
      have hlastIndex : b - 1 < window.length := by omega
      let kLast : Fin window.length := ⟨b - 1, hlastIndex⟩
      let lastCell := ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
        rate source rewards C_star C_h hc count hspan kLast
      have hlastCellInput : cells[b - 1] = lastCell.input := by
        simpa [cells, lastCell, kLast] using
          ReferenceFirstWindowNumericalStream.actualLiveSourceCells_get
            rate source rewards C_star C_h hc count hspan kLast
      have hlastSplit :
          Da b = Da (b - 1) ++
            [(lastCell.input.enabled, RecordedQueueRun.quantizedArrival
              (ReferenceFirstLaunchNumericalCell.queueParameters rate) lastCell.input a.1)] := by
        unfold Da
        have hcellIndex : b - 1 < cells.length := by
          rw [hcellsLength]
          exact kLast.isLt
        rw [show b = (b - 1) + 1 by omega,
          List.take_succ_eq_append_getElem hcellIndex, List.map_append]
        congr 1
        simp [hlastCellInput]
      have hprevReplay : owned.previousService a =
          CollectionKnownQueueContinuation.replayLastService (4 * rate.n) (0, 0) 0 (Da b) := by
        simpa [Da, hrecords] using hpreviousWindow
      have hprevService := replayLastService_append_one (4 * rate.n) (0, 0) 0
        (Da (b - 1))
        (lastCell.input.enabled,
          RecordedQueueRun.quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate)
            lastCell.input a.1)
      have hprevService' : owned.previousService a =
          RecordedQueueRun.recordService (4 * rate.n) (Va (b - 1))
            (lastCell.input.enabled, RecordedQueueRun.quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate)
              lastCell.input a.1) := by
        rw [hprevReplay, hlastSplit, hprevService]
      have htransition : QueueReplay.transition (4 * rate.n) (Va (b - 1))
          (lastCell.input.enabled, RecordedQueueRun.quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate)
            lastCell.input a.1) = Va b := by
        unfold Va
        rw [hlastSplit, QueueReplay.replay_append]
        simp [QueueReplay.replay]
      have hdiff : (Va b).1 - (Va (b - 1)).1 =
          RecordedQueueRun.recordService (4 * rate.n) (Va (b - 1))
            (lastCell.input.enabled, RecordedQueueRun.quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate)
              lastCell.input a.1) := by
        rw [← htransition, RecordedQueueRun.transition_score_eq_add_recordService]
        exact Nat.add_sub_cancel_left _ _
      have hdomains : r.complementScores a ≤ p.T * D p ∧
          owned.queue a ≤ p.T * D p ∧ owned.previousService a ≤ D p := by
        have hlastFin : (b - 1 : ℕ) < window.length := by omega
        have hspanSucc : start + (b - 1 + 1) ≤ p.T := by omega
        let last : Fin window.length := ⟨b - 1, hlastFin⟩
        let lastRecord := window[last.val]'last.isLt
        have hlastRunBound : last.val < run.records.length :=
          lt_of_lt_of_le last.isLt hwindowPrefix.length_le
        have hlastPrefixElem : window[last.val]'last.isLt = run.records[last.val]'hlastRunBound :=
          hwindowPrefix.getElem last.isLt
        have hlastMem : lastRecord ∈ run.records := by
          change window[last.val] ∈ run.records
          rw [hlastPrefixElem]
          exact List.getElem_mem hlastRunBound
        have hrecordAtMemSucc :
            ReferenceAssignmentPayloadChronology.actualRunRecordAt initial rows selectedRow rewards
              start (b - 1) hspanSucc seed.activeAtStart ∈
              (ReferenceActivePhysicalHorizon.run initial rows selectedRow rewards
                start (b - 1 + 1) hspanSucc seed.activeAtStart).records := by
          rw [ReferenceAssignmentPayloadChronology.run_successor_actualRunRecordAt]
          exact List.mem_append_right _ (by simp [ReferenceAssignmentPayloadChronology.actualRunRecordAt])
        have hrecordAtMemB :
            ReferenceAssignmentPayloadChronology.actualRunRecordAt initial rows selectedRow rewards
              start (b - 1) hspanSucc seed.activeAtStart ∈
              (ReferenceActivePhysicalHorizon.run initial rows selectedRow rewards
                start b hspanB seed.activeAtStart).records := by
          simpa [Nat.sub_add_cancel hbpos] using hrecordAtMemSucc
        have hrecordAtMem :
            ReferenceAssignmentPayloadChronology.actualRunRecordAt initial rows selectedRow rewards
              start (b - 1) hspanSucc seed.activeAtStart ∈ run.records :=
          prefix_mem b hbcount _ (by simpa [hrun] using hrecordAtMemB)
        have htimes := ReferenceActivePhysicalHorizon.run_time_values initial rows selectedRow
          rewards start count hspan seed.activeAtStart
        have hmapTimes : run.records.map (fun z => z.input.time.val) =
            ReferenceActivePhysicalHorizon.calendar start count := by
          simpa [hrun] using htimes
        have hmapBound : last.val < (run.records.map (fun z => z.input.time.val)).length := by
          simpa using hlastRunBound
        have hcalendarBound : last.val <
            (ReferenceActivePhysicalHorizon.calendar start count).length := by
          simpa [ReferenceActivePhysicalHorizon.calendar] using
            (show last.val < count by omega)
        have hlastTime : lastRecord.input.time.val = start + (b - 1) := by
          calc
            lastRecord.input.time.val = run.records[last.val].input.time.val := by
              change window[last.val].input.time.val = _
              rw [hlastPrefixElem]
            _ = (run.records.map (fun z => z.input.time.val))[last.val] := by
              simp [hmapBound]
            _ = (ReferenceActivePhysicalHorizon.calendar start count)[last.val] :=
              List.getElem_of_eq hmapTimes hmapBound
            _ = start + (b - 1) := by
              simp [last, ReferenceActivePhysicalHorizon.calendar, hcalendarBound]
        have hlastRecordEq : lastRecord =
            ReferenceAssignmentPayloadChronology.actualRunRecordAt initial rows selectedRow rewards
              start (b - 1) hspanSucc seed.activeAtStart :=
          ReferenceAssignmentPayloadChronology.run_records_time_injective
            initial rows selectedRow rewards start count hspan seed.activeAtStart
            hlastMem hrecordAtMem (by rw [hlastTime]; rfl)
        have hfinalSucc := ReferenceAssignmentPayloadChronology.run_successor_finalState_eq_actualRunRecordAt
          initial rows selectedRow rewards start (b - 1) hspanSucc seed.activeAtStart
        have hfinalB :
            (ReferenceActivePhysicalHorizon.run initial rows selectedRow rewards
              start b hspanB seed.activeAtStart).finalState =
              (ReferenceAssignmentPayloadChronology.actualRunRecordAt initial rows selectedRow rewards
                start (b - 1) hspanSucc seed.activeAtStart).output.next := by
          simpa [Nat.sub_add_cancel hbpos] using hfinalSucc
        have hlastNext :
            (ReferenceActivePhysicalHorizon.run initial rows selectedRow rewards
              start b hspanB seed.activeAtStart).finalState.coordinator =
              lastRecord.output.next.coordinator := by
          calc
            _ = (ReferenceAssignmentPayloadChronology.actualRunRecordAt initial rows selectedRow rewards
                start (b - 1) hspanSucc seed.activeAtStart).output.next.coordinator :=
              congrArg ReferenceActivePhysicalStep.State.coordinator hfinalB
            _ = lastRecord.output.next.coordinator := by rw [hlastRecordEq]
        have hbranch :=
          ReferenceFirstLiveCoordinatorNumericalService.actual_first_live_coordinator_service_branches
            rate source rewards C_star C_h hc count hspan last
        have hnum :=
          ReferenceFirstLiveCoordinatorNumericalService.actual_first_live_coordinator_numerical_service
            rate source rewards C_star C_h hc count hspan last
        dsimp only at hnum
        rcases hbranch with hfirst | hcontinuing
        · rcases hfirst with ⟨installed, selected, hbranch, htime⟩
          rw [hbranch] at hnum
          rcases hnum with ⟨recording, serviced, pending, finished,
            _hrun, _hrecording, hservice, _hpayload, _henabled,
            _harrival, _hfields, hdomain, _hzero, _hconfirmation, _hfinish,
            _hfinishedPending, _hfailure, _hup, _hbank, hnext⟩
          let nextRegisters : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta := {
            payload := installed.registers.payload
            priorClock := finished.clock
            pendingAtChoice := finished.pending
            time := lastRecord.input.time
            gridBoundary := finished.clock.g
            complementScores := serviced.score }
          let nextOwned : CoordinatorLiveServiceFinish.OwnedRegisters nextRegisters := {
            queue := serviced.queue, previousService := serviced.previousService }
          have hcfg : ReferenceActivePhysicalStep.CoordinatorConfiguration.live r owned base =
              ReferenceActivePhysicalStep.CoordinatorConfiguration.live nextRegisters nextOwned
                installed.followerBaseScore := by
            calc
              _ = (ReferenceActivePhysicalHorizon.run initial rows selectedRow rewards
                    start b hspanB seed.activeAtStart).finalState.coordinator := by
                simpa [initial, start] using hlive.symm
              _ = lastRecord.output.next.coordinator := hlastNext
              _ = _ := by simpa [nextRegisters, nextOwned] using hnext
          have hfields := ReferenceActivePhysicalStep.CoordinatorConfiguration.live.inj hcfg
          have hregsEq := hfields.1
          have hownedEq := hfields.2.1
          subst r
          cases hownedEq
          refine ⟨?_, ?_, ?_⟩
          · exact (hdomain a).2.2.2.1
          · exact (hdomain a).2.2.1
          · exact (hdomain a).2.2.2.2
        · rcases hcontinuing with
            ⟨registers, ownedNow, baseNow, dispatched, hstart, continuation, selected, hbranch⟩
          rw [hbranch] at hnum
          rcases hnum with ⟨recording, serviced, pending, finished,
            _hrun, _hrecording, hservice, _hpayload, _henabled,
            _harrival, _hfields, hdomain, _hzero, _hconfirmation, _hfinish,
            _hfinishedPending, _hfailure, _hup, _hbank, hnext⟩
          let actualRegisters := ReferenceActivePhysicalStep.liveRegistersAt registers lastRecord.input.time
          let nextRegisters : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta := {
            payload := actualRegisters.payload
            priorClock := finished.clock
            pendingAtChoice := finished.pending
            time := lastRecord.input.time
            gridBoundary := finished.clock.g
            complementScores := serviced.score }
          let nextOwned : CoordinatorLiveServiceFinish.OwnedRegisters nextRegisters := {
            queue := serviced.queue, previousService := serviced.previousService }
          have hcfg : ReferenceActivePhysicalStep.CoordinatorConfiguration.live r owned base =
              ReferenceActivePhysicalStep.CoordinatorConfiguration.live nextRegisters nextOwned baseNow := by
            calc
              _ = (ReferenceActivePhysicalHorizon.run initial rows selectedRow rewards
                    start b hspanB seed.activeAtStart).finalState.coordinator := by
                simpa [initial, start] using hlive.symm
              _ = lastRecord.output.next.coordinator := hlastNext
              _ = _ := by simpa [nextRegisters, nextOwned] using hnext
          have hfields := ReferenceActivePhysicalStep.CoordinatorConfiguration.live.inj hcfg
          have hregsEq := hfields.1
          have hownedEq := hfields.2.1
          subst r
          cases hownedEq
          refine ⟨?_, ?_, ?_⟩
          · exact (hdomain a).2.2.2.1
          · exact (hdomain a).2.2.1
          · exact (hdomain a).2.2.2.2
      refine ⟨hrecords, ?_, hstateReplay, ?_, hdomains.1, hdomains.2.1,
        hdomains.2.2, ?_⟩
      · intro d hd
        have hd' : d ∈ ReferenceFirstComplementReplay.liveDiagnosticQueueRecords
            r.payload a.1 window b := by
          simpa [window, run, hwindow, hrun] using hd
        exact hDenabledWindow d hd'
      · rw [hprevService']
        exact hdiff.symm
      · intro k
        let k' : Fin window.length := ⟨k.val, lt_of_lt_of_le k.isLt hbWindow⟩
        let cell := ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
          rate source rewards C_star C_h hc count hspan k'
        have hmem :
            ReferenceFirstComplementReplay.liveDiagnosticQueueRecord r.payload a.1 window[k.val] ∈
              ReferenceFirstComplementReplay.liveDiagnosticQueueRecords r.payload a.1 window b :=
          List.mem_map.mpr ⟨window[k.val], by
            have hkTake : k.val < (window.take b).length := by
              simpa [List.length_take, Nat.min_eq_left hbWindow] using k.isLt
            have htakeMem : (window.take b)[k.val] ∈ window.take b :=
              List.getElem_mem hkTake
            have htakeElem : (window.take b)[k.val] = window[k.val] := by
              simp [List.getElem_take, k.isLt]
            rw [← htakeElem]
            exact htakeMem, rfl⟩
        have henabled := hDenabled _ hmem
        have hjoin := current_live_diagnostic_cell_join rate source rewards C_star C_h
          hc count hspan k' r.payload (payload_at ⟨k.val, k.isLt⟩) a henabled
        exact hjoin

end Bandits.Support.ReferenceFirstLiveComplementQueueReplay

end
