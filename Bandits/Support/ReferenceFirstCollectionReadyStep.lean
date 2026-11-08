/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedFirstCollectionAdmissionBoundary

import Lean.Elab.Tactic.Omega

/-!
# One actual first-collection ready step

This module develops one local continuing-collection step at an actual record
of the original finite reference execution.  Its only induction premise is
the existing literal ready domain at that record.  It does not assume that a
message is accepted, or that any ready-state family exists over the stream.

Mathematical source ranges: `sources/zip4/manuscript/06_interruptions.tex:9-100,
246-299`, `sources/zip4/manuscript/04_slow_fast_learner.tex:157-174`,
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-70`, and
`sources/zip4/manuscript/07_public_setup.tex:127-164`.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions

namespace Bandits.Support.ReferenceFirstCollectionReadyStep

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev SourceInput := BootstrapPrivateRoundStreams.SourceInput
abbrev RewardTable := ActualInitializationPhysicalStep.GridRewardTable
abbrev Record (p : Parameters) (rate : RateInput p) :=
  ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)
abbrev Payload {p : Parameters} (rate : RateInput p) :=
  ReferenceActivePhysicalStep.Payload rate
abbrev Ledger {p : Parameters} (rate : RateInput p) :=
  ReferenceActivePhysicalStep.Ledger rate

variable {p : Parameters} {rate : RateInput p}

private theorem run_record_endpoints
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p)
    (selected : Fin (ConstructorDimensions.M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (j : ℕ) (hj : j < count) :
    ((ReferenceActivePhysicalHorizon.run initial rows selected rewards start count
      hspan active).records[j]'(by
        rw [ReferenceActivePhysicalHorizon.run_record_count]; exact hj)).input.state =
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start j
        (by omega) active).finalState ∧
    (ReferenceActivePhysicalHorizon.run initial rows selected rewards start (j + 1)
      (by omega) active).finalState =
      ((ReferenceActivePhysicalHorizon.run initial rows selected rewards start count
        hspan active).records[j]'(by
          rw [ReferenceActivePhysicalHorizon.run_record_count]; exact hj)).output.next := by
  let actual := ReferenceAssignmentPayloadChronology.actualRunRecordAt initial rows selected
    rewards start j (by omega) active
  have hsuccessorRecords := ReferenceAssignmentPayloadChronology.run_successor_actualRunRecordAt
    initial rows selected rewards start j (by omega) active
  have hsuccessorFinal := ReferenceAssignmentPayloadChronology.run_successor_finalState_eq_actualRunRecordAt
    initial rows selected rewards start j (by omega) active
  obtain ⟨suffix, hprefix⟩ := ReferenceCollectionPhaseHistory.run_records_prefix
    initial rows selected rewards start (j + 1) (count - (j + 1)) (by omega) active
  have hprefixCount :
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count
        hspan active).records =
        (ReferenceActivePhysicalHorizon.run initial rows selected rewards start (j + 1)
          (by omega) active).records ++ suffix := by
    simpa [Nat.add_sub_of_le (by omega : j + 1 ≤ count)] using hprefix
  have hjFull : j < (ReferenceActivePhysicalHorizon.run initial rows selected rewards start
      count hspan active).records.length := by
    rw [ReferenceActivePhysicalHorizon.run_record_count]
    exact hj
  have hjSuccessor : j < (ReferenceActivePhysicalHorizon.run initial rows selected rewards start
      (j + 1) (by omega) active).records.length := by
    rw [ReferenceActivePhysicalHorizon.run_record_count]
    omega
  have hprefixAt := List.getElem_of_eq hprefixCount hjFull
  have hsuccessorAt := List.getElem_of_eq hsuccessorRecords hjSuccessor
  have hprefixAt' :
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count
        hspan active).records.get ⟨j, hjFull⟩ =
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start (j + 1)
        (by omega) active).records.get ⟨j, hjSuccessor⟩ := by
    simpa [List.getElem_append, ReferenceActivePhysicalHorizon.run_record_count] using hprefixAt
  have hsuccessorAt' :
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start (j + 1)
        (by omega) active).records.get ⟨j, hjSuccessor⟩ = actual := by
    simpa [actual, List.getElem_append, ReferenceActivePhysicalHorizon.run_record_count] using
      hsuccessorAt
  have hactual :
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count
        hspan active).records.get ⟨j, hjFull⟩ = actual :=
    hprefixAt'.trans hsuccessorAt'
  constructor
  · change ((ReferenceActivePhysicalHorizon.run initial rows selected rewards start count
        hspan active).records.get ⟨j, hjFull⟩).input.state = _
    rw [hactual]
    rfl
  · change (ReferenceActivePhysicalHorizon.run initial rows selected rewards start (j + 1)
        (by omega) active).finalState =
      ((ReferenceActivePhysicalHorizon.run initial rows selected rewards start count
        hspan active).records.get ⟨j, hjFull⟩).output.next
    rw [hactual]
    exact hsuccessorFinal

private theorem run_record_eq_actual
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p)
    (selected : Fin (ConstructorDimensions.M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (j : ℕ) (hj : j < count) :
    (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count
      hspan active).records[j]'(by
        rw [ReferenceActivePhysicalHorizon.run_record_count]; exact hj) =
      ReferenceAssignmentPayloadChronology.actualRunRecordAt initial rows selected
        rewards start j (by omega) active := by
  let full := ReferenceActivePhysicalHorizon.run initial rows selected rewards start count
    hspan active
  let pref := ReferenceActivePhysicalHorizon.run initial rows selected rewards start (j + 1)
    (by omega) active
  let actual := ReferenceAssignmentPayloadChronology.actualRunRecordAt initial rows selected
    rewards start j (by omega) active
  obtain ⟨suffix, hprefix⟩ := ReferenceCollectionPhaseHistory.run_records_prefix
    initial rows selected rewards start (j + 1) (count - (j + 1)) (by omega) active
  have hprefixCount : full.records = pref.records ++ suffix := by
    simpa [full, pref, Nat.add_sub_of_le (by omega : j + 1 ≤ count)] using hprefix
  have hsuccessor := ReferenceAssignmentPayloadChronology.run_successor_actualRunRecordAt
    initial rows selected rewards start j (by omega) active
  have hjFull : j < full.records.length := by
    rw [ReferenceActivePhysicalHorizon.run_record_count]
    exact hj
  have hjPrefix : j < pref.records.length := by
    rw [ReferenceActivePhysicalHorizon.run_record_count]
    omega
  have hfullAt := List.getElem_of_eq hprefixCount hjFull
  have hprefixAt := List.getElem_of_eq hsuccessor hjPrefix
  have hfullPrefix : full.records[j]'hjFull = pref.records[j]'hjPrefix := by
    simpa [List.getElem_append, ReferenceActivePhysicalHorizon.run_record_count,
      hjPrefix] using hfullAt
  have hprefixActual : pref.records[j]'hjPrefix = actual := by
    simpa [pref, actual, List.getElem_append,
      ReferenceActivePhysicalHorizon.run_record_count, hjPrefix] using hprefixAt
  simpa [full] using hfullPrefix.trans hprefixActual

private theorem round_input_ext
    {left right : ReferenceActivePhysicalStep.RoundInput p rate}
    (hstate : left.state = right.state) (hrows : left.rows = right.rows)
    (hselected : left.selected = right.selected) (htime : left.time = right.time)
    (hrewards : left.rewards = right.rewards) : left = right := by
  cases left
  cases right
  cases hstate
  cases hrows
  cases hselected
  cases htime
  cases hrewards
  rfl

/-- The requested collection window is indexed inside the actual epoch run.
The output equality is the canonical record field, not a separately supplied
step-equality premise. -/
theorem actual_collection_window_record_alignment
    (rate : RateInput p) (source : SourceInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (count : ℕ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (hspan : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed + count ≤ p.T)
    (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
        rate source rewards C_star C_h hcross count hspan).records).length < count)
    (n : Fin (ReferenceCollectionPhaseHistory.collectionWindow
      (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
        rate source rewards C_star C_h hcross count hspan).records
      (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
          rate source rewards C_star C_h hcross count hspan).records).length).length) :
    let start := ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
    let epoch := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
      rate source rewards C_star C_h hcross count hspan
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow epoch.records).length
    let window := ReferenceCollectionPhaseHistory.collectionWindow epoch.records w
    epoch.records[w + n.val]? = some window[n.val] ∧
      window[n.val].input.time.val + 1 = start + w + 1 + n.val ∧
      window[n.val].output = ReferenceActivePhysicalStep.step window[n.val].input := by
  let start := ReferenceInitializationRun.elapsed p
    (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
  let epoch := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
    rate source rewards C_star C_h hcross count hspan
  let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow epoch.records).length
  let window := ReferenceCollectionPhaseHistory.collectionWindow epoch.records w
  have htime := ReferenceFirstCollectionEpochAlignment.actual_first_collection_window_time
    rate source rewards C_star C_h count hcross hspan hshort n
  change epoch.records[w + n.val]? = some window[n.val] ∧
    window[n.val].input.time.val + 1 = start + w + 1 + n.val ∧
    window[n.val].output = ReferenceActivePhysicalStep.step window[n.val].input
  simpa only [start, epoch, w, window] using
    ⟨htime.1, htime.2, window[n.val].output_eq⟩

/-- The actual record at this window coordinate is the output of its literal
prefix run, and its next state is the endpoint of the next prefix. -/
theorem actual_collection_window_prefix_endpoints
    (rate : RateInput p) (source : SourceInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (count : ℕ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (hspan : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed + count ≤ p.T)
    (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
        rate source rewards C_star C_h hcross count hspan).records).length < count)
    (n : Fin (ReferenceCollectionPhaseHistory.collectionWindow
      (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
        rate source rewards C_star C_h hcross count hspan).records
      (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
          rate source rewards C_star C_h hcross count hspan).records).length).length) :
    let start := ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
    let initial := ReferenceFirstCollectionEpochAlignment.actualLaunchState
      rate source rewards C_star C_h hcross
    let epoch := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
      rate source rewards C_star C_h hcross count hspan
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow epoch.records).length
    let window := ReferenceCollectionPhaseHistory.collectionWindow epoch.records w
    let r := window[n.val]
    let j := w + n.val
    r.input.state = (ReferenceActivePhysicalHorizon.run initial source.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start j
      (by
        have htime := actual_collection_window_record_alignment rate source rewards
          C_star C_h count hcross hspan hshort n
        have htimeEq := htime.2
        have htimeLt := window[n.val].input.time.isLt
        dsimp [start, epoch, w, window, r, j] at htimeEq htimeLt ⊢
        omega)
      (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
        rate source rewards C_star C_h hcross).1).finalState ∧
    (ReferenceActivePhysicalHorizon.run initial source.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start (j + 1)
      (by
        have htime := actual_collection_window_record_alignment rate source rewards
          C_star C_h count hcross hspan hshort n
        have htimeEq := htime.2
        have htimeLt := window[n.val].input.time.isLt
        dsimp [start, epoch, w, window, r, j] at htimeEq htimeLt ⊢
        omega)
      (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
        rate source rewards C_star C_h hcross).1).finalState = r.output.next := by
  let start := ReferenceInitializationRun.elapsed p
    (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
  let initial := ReferenceFirstCollectionEpochAlignment.actualLaunchState
    rate source rewards C_star C_h hcross
  let epoch := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
    rate source rewards C_star C_h hcross count hspan
  let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow epoch.records).length
  let window := ReferenceCollectionPhaseHistory.collectionWindow epoch.records w
  let r := window[n.val]
  let j := w + n.val
  have hlookup := actual_collection_window_record_alignment rate source rewards
    C_star C_h count hcross hspan hshort n
  dsimp [start, epoch, w, window, r, j] at hlookup
  obtain ⟨hrecordLookup, htime, _hstep⟩ := hlookup
  have hindex : w + n.val < epoch.records.length :=
    (List.getElem?_eq_some_iff.mp hrecordLookup).1
  have hcount : epoch.records.length = count := by
    simpa [epoch, ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun] using
      ReferenceActivePhysicalHorizon.run_record_count initial source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start count hspan
        (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
          rate source rewards C_star C_h hcross).1
  have hj : w + n.val < count := by
    calc
      w + n.val < epoch.records.length := hindex
      _ = count := hcount
  have hendpoints := run_record_endpoints initial source.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start count hspan
    (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
      rate source rewards C_star C_h hcross).1 (w + n.val) hj
  have hrecord : epoch.records[w + n.val] = r := by
    exact Option.some.inj ((List.getElem?_eq_getElem hindex).symm.trans hrecordLookup)
  constructor
  · calc
      r.input.state = epoch.records[w + n.val].input.state := by rw [hrecord]
      _ = (ReferenceActivePhysicalHorizon.run initial source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start
        (w + n.val) (by omega)
        (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
          rate source rewards C_star C_h hcross).1).finalState := hendpoints.1
  · calc
      (ReferenceActivePhysicalHorizon.run initial source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start
        (w + n.val + 1) (by omega)
        (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
          rate source rewards C_star C_h hcross).1).finalState =
          epoch.records[w + n.val].output.next := hendpoints.2
      _ = r.output.next := by rw [hrecord]

/-- Produce the real continuing collection dispatch, recorder, and START at
the selected actual window record from its literal ready domain. -/
theorem actual_collection_window_ready_start
    (rate : RateInput p) (source : SourceInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (count : ℕ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (hspan : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed + count ≤ p.T)
    (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
        rate source rewards C_star C_h hcross count hspan).records).length < count)
    (n : Fin (ReferenceCollectionPhaseHistory.collectionWindow
      (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
        rate source rewards C_star C_h hcross count hspan).records
      (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
          rate source rewards C_star C_h hcross count hspan).records).length).length)
    (payload : Payload rate) (ledger : Ledger rate)
    (saved : Option (Fin p.T × Bool))
    (hReady : ReferenceContinuingCollectionStartDomains.continuingCollectionReadyDomain
      (ReferenceCollectionPhaseHistory.collectionWindow
        (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
          rate source rewards C_star C_h hcross count hspan).records
        (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
          (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
            rate source rewards C_star C_h hcross count hspan).records).length)[n.val].input
      payload ledger saved) :
    let start := ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
    let epoch := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
      rate source rewards C_star C_h hcross count hspan
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow epoch.records).length
    let window := ReferenceCollectionPhaseHistory.collectionWindow
      epoch.records w
    let x := window[n.val].input
    window[n.val].output = ReferenceActivePhysicalStep.step x ∧
    window[n.val].input.time.val + 1 = start + w + 1 + n.val ∧
    ∃ cutoff : Fin p.T, cutoff.val + 1 = ledger.cutoff ∧
    let clock := ReferenceActivePhysicalStep.collectionClock payload ledger saved cutoff
    let input := ReferenceActivePhysicalStep.collectionInput x payload ledger clock cutoff
    ∃ (core : CoordinatorRoundDispatch.CollectionCoreValid input)
      (snap : CoordinatorCollectionInteractive.PreparedSnapshot input)
      (hb : snap.clockStarted.clock.g ≤ p.T + 1)
      (hs : CoordinatorRoundDispatch.collectionCurrentScoresCheck input = true),
      (ReferenceActivePhysicalStep.prepare x).coordinator =
        .collection payload ledger clock cutoff (.continuing core snap hb hs) ∧
      ∃ (c : ReferenceCollectionSegmentExtraction.Choice rate)
        (o : CoordinatorRecordingOperation.Output p) (started : Ledger rate),
        ReferenceCollectionSegmentExtraction.choice x = some c ∧
        CoordinatorRecorderComplementBridge.run
          (ReferenceActivePhysicalStep.collectionRecordingInput
            (ReferenceActivePhysicalStep.prepare x) c.payload c.started c.weights) = some o ∧
        c.payload = payload ∧ c.preLedger = ledger ∧
        c.started = snap.clockStarted ∧ c.initializer = none ∧
        CoordinatorCollectionLedger.startRound ledger (x.time.val + 1)
          (ReferenceActivePhysicalStep.collectionEnabled ledger x.time)
          (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder o) =
            .success started ∧
        started = CoordinatorCollectionLedger.startRoundCandidate c.preLedger x.time
          (ReferenceActivePhysicalStep.collectionEnabled c.preLedger x.time)
          (ReferenceCollectionRawBufferHistory.rawDiagnostic window[n.val]) ∧
        (∀ a, (started.currentRegisters a = none ↔
            CoordinatorCollectionLedger.armPending started a) ∧
          (started.cutoffRegisters a = none ↔
            CoordinatorCollectionLedger.armPending started a)) := by
  classical
  let start := ReferenceInitializationRun.elapsed p
    (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
  let initial := ReferenceFirstCollectionEpochAlignment.actualLaunchState
    rate source rewards C_star C_h hcross
  let epoch := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
    rate source rewards C_star C_h hcross count hspan
  let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow epoch.records).length
  let window := ReferenceCollectionPhaseHistory.collectionWindow epoch.records w
  let x := window[n.val].input
  obtain ⟨cutoff, hcutoff, core, snap, hb, hs, hcoord, harm, hlocal,
    hrecordInputs, o, started, hrecording, hstart, hcandidate, hvalid,
    hphase, hcursor, hσ, hcutoffLedger, hfreeze, hpending, hassignment,
    hbase, hcutRegisters, hincrement, hregisters, hobserve,
    hrecordingObserve, hdiagnostic, hdomain, hinputCheck, hbankInput,
    hmessages⟩ :=
      ReferenceContinuingCollectionAcceptedFinishDomains.continuing_collection_accepted_finish_domains
        x payload ledger saved hReady
  let input := ReferenceActivePhysicalStep.collectionInput x payload ledger
    (ReferenceActivePhysicalStep.collectionClock payload ledger saved cutoff) cutoff
  let weights := CoordinatorCollectionInteractive.PreObservationInputs.weights input
    snap.inputsValid.ledger_valid snap.inputsValid.assignment_eq
  let c : ReferenceCollectionSegmentExtraction.Choice rate :=
    ⟨payload, ledger, snap.clockStarted, weights, none⟩
  have hchoice : ReferenceCollectionSegmentExtraction.choice x = some c := by
    unfold ReferenceCollectionSegmentExtraction.choice
    rw [hcoord]
    simp [ReferenceCollectionSegmentExtraction.choiceOfCut,
      ReferenceActivePhysicalStep.DispatchCut.selection, c, weights, input]
  have hrecordedChoice : CoordinatorRecorderComplementBridge.run
      (ReferenceActivePhysicalStep.collectionRecordingInput
        (ReferenceActivePhysicalStep.prepare x) c.payload c.started c.weights) = some o := by
    simpa [c, input, weights] using hrecording
  let r := window[n.val]
  have hrecordingActual : r.output.coordinator.recording = some o := by
    rw [r.output_eq]
    change (ReferenceActivePhysicalStep.prepare x).observeCoordinator.recording = some o
    exact hrecordingObserve
  have hraw : CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder o =
      ReferenceCollectionRawBufferHistory.rawDiagnostic r := by
    simp [ReferenceCollectionRawBufferHistory.rawDiagnostic, hrecordingActual,
      CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder]
  have hcandidateActual : started =
      CoordinatorCollectionLedger.startRoundCandidate c.preLedger x.time
        (ReferenceActivePhysicalStep.collectionEnabled c.preLedger x.time)
        (ReferenceCollectionRawBufferHistory.rawDiagnostic r) := by
    calc
      started = CoordinatorCollectionLedger.startRoundCandidate ledger x.time
          (ReferenceActivePhysicalStep.collectionEnabled ledger x.time)
          (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder o) := hcandidate
      _ = CoordinatorCollectionLedger.startRoundCandidate c.preLedger x.time
          (ReferenceActivePhysicalStep.collectionEnabled c.preLedger x.time)
          (ReferenceCollectionRawBufferHistory.rawDiagnostic r) := by
        simp [c, hraw]
  have hstartActual : CoordinatorCollectionLedger.startRound ledger (x.time.val + 1)
      (ReferenceActivePhysicalStep.collectionEnabled ledger x.time)
      (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder o) =
        .success started := by
    simpa [ReferenceContinuingCollectionAcceptedFinishDomains.sourceRound] using hstart
  have hactualAlignment := actual_collection_window_record_alignment rate source rewards
    C_star C_h count hcross hspan hshort n
  have hactualStep : window[n.val].output = ReferenceActivePhysicalStep.step x := by
    simpa [start, epoch, w, window, x] using hactualAlignment.2.2
  have hactualTime : window[n.val].input.time.val + 1 = start + w + 1 + n.val := by
    simpa [start, epoch, w, window, x] using hactualAlignment.2.1
  refine ⟨hactualStep, hactualTime, cutoff, hcutoff, core, snap, hb, hs, hcoord, c, o, started,
    hchoice, hrecordedChoice, rfl, rfl, rfl, rfl, hstartActual,
    ?_, hregisters⟩
  simpa [x, r] using hcandidateActual

/-- Construct the next literal original-prefix input when it lies strictly
before the horizon.  When its physical record is present, this is that exact
record's input. -/
theorem actual_collection_window_next_prefix_input
    (rate : RateInput p) (source : SourceInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (count : ℕ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (hspan : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed + count ≤ p.T)
    (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
        rate source rewards C_star C_h hcross count hspan).records).length < count)
    (n : Fin (ReferenceCollectionPhaseHistory.collectionWindow
      (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
        rate source rewards C_star C_h hcross count hspan).records
      (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
          rate source rewards C_star C_h hcross count hspan).records).length).length)
    (hbefore :
      (ReferenceCollectionPhaseHistory.collectionWindow
        (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
          rate source rewards C_star C_h hcross count hspan).records
        (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
          (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
            rate source rewards C_star C_h hcross count hspan).records).length)[n.val].input.time.val + 1 < p.T) :
    let start := ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
    let initial := ReferenceFirstCollectionEpochAlignment.actualLaunchState
      rate source rewards C_star C_h hcross
    let epoch := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
      rate source rewards C_star C_h hcross count hspan
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow epoch.records).length
    let window := ReferenceCollectionPhaseHistory.collectionWindow epoch.records w
    let r := window[n.val]
    let j := w + n.val
    ∃ next : ReferenceActivePhysicalStep.RoundInput p rate,
      next.state = r.output.next ∧
      next.rows = source.1.2 ∧
      next.selected = ActualInitializationPhysicalStep.selectedRowIndex p source ∧
      next.rewards = rewards ∧
      next.time.val = start + j + 1 ∧
      ∀ (hnext : j + 1 < count),
        next = (epoch.records[j + 1]'(by
          have htime := actual_collection_window_record_alignment rate source rewards
            C_star C_h count hcross hspan hshort n
          dsimp [start, epoch, w, window, r, j] at htime
          have hcount : epoch.records.length = count := by
            simpa [epoch, ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun] using
              ReferenceActivePhysicalHorizon.run_record_count initial source.1.2
                (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start count hspan
                (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
                  rate source rewards C_star C_h hcross).1
          omega)).input := by
  classical
  let start := ReferenceInitializationRun.elapsed p
    (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
  let initial := ReferenceFirstCollectionEpochAlignment.actualLaunchState
    rate source rewards C_star C_h hcross
  let active := (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
    rate source rewards C_star C_h hcross).1
  let epoch := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
    rate source rewards C_star C_h hcross count hspan
  let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow epoch.records).length
  let window := ReferenceCollectionPhaseHistory.collectionWindow epoch.records w
  let r := window[n.val]
  let j := w + n.val
  have hlookup := actual_collection_window_record_alignment rate source rewards
    C_star C_h count hcross hspan hshort n
  have hnextTime : r.input.time.val + 1 = start + j + 1 := by
    have h := hlookup.2.1
    change r.input.time.val + 1 = start + w + 1 + n.val at h
    dsimp [j]
    omega
  have hbefore' : r.input.time.val + 1 < p.T := by
    simpa [start, epoch, w, window, r, j] using hbefore
  have hnextSpan : start + (j + 1) ≤ p.T := by
    omega
  have hcount : epoch.records.length = count := by
    simpa [epoch, ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun] using
      ReferenceActivePhysicalHorizon.run_record_count initial source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start count hspan active
  have hj : j < count := by
    have hindex : j < epoch.records.length :=
      (List.getElem?_eq_some_iff.mp (by
        simpa [start, epoch, w, window, r, j] using hlookup.1)).1
    omega
  let nextRun := ReferenceActivePhysicalHorizon.run initial source.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start (j + 1)
    hnextSpan active
  let next := ReferenceActivePhysicalHorizon.roundInputAt initial source.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start active nextRun
    ⟨start + j + 1, by omega, by omega⟩
  have hstate : next.state = r.output.next := by
    dsimp [next, ReferenceActivePhysicalHorizon.roundInputAt, nextRun]
    have hprefixEndpoints := actual_collection_window_prefix_endpoints rate source rewards
      C_star C_h count hcross hspan hshort n
    simpa [start, initial, epoch, w, window, r, j, active,
      ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun] using hprefixEndpoints.2
  refine ⟨next, hstate, rfl, rfl, rfl, ?_, ?_⟩
  · simp [next, ReferenceActivePhysicalHorizon.roundInputAt, start, j, w, epoch,
      ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun]
  · intro hnext
    have hrecordActual := run_record_eq_actual initial source.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start count hspan active
      (j + 1) hnext
    have hindex : j + 1 < epoch.records.length := by
      rw [hcount]
      exact hnext
    change next = (epoch.records[j + 1]'hindex).input
    have hrecordActual' : epoch.records[j + 1]'hindex =
        ReferenceAssignmentPayloadChronology.actualRunRecordAt initial source.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start (j + 1)
          (by omega) active := by
      simpa [epoch, ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun] using
        hrecordActual
    rw [hrecordActual']
    rfl

end Bandits.Support.ReferenceFirstCollectionReadyStep

end
