/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLiveSourceCellReadout
public import Bandits.Support.ReferenceFirstLiveStoppedQueueComparison

import Lean.Elab.Tactic.Omega
import Mathlib.Data.List.Basic

/-!
# Actual chronological first-live retained queue update

Sources: `sources/zip4/manuscript/04_slow_fast_learner.tex:140-188`,
`sources/zip4/manuscript/05_binary_transport.tex:354-431`,
`sources/zip4/manuscript/06_interruptions.tex:391-408,425-426`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-64`.

This module joins C's current original-source cell to the literal stopped
queue update on its complete chronological cell list. It also joins that
update to M's original-source saved readout and, before the first overflow,
to the same actual physical endpoint after the current round. It asserts no
conditional recording law or manuscript-history identification.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceAssignmentPayloadPersistence

namespace Bandits.Support.ReferenceFirstLiveChronologicalRetainedUpdate

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev RewardTable := ActualInitializationPhysicalStep.GridRewardTable
abbrev TimeControl := ContinuousLearningRows.TimeControl

variable {p : Parameters} (rate : RateInput p) (rewards : RewardTable p)
  (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T)
  (s : ℕ) (hs : s ≤ t.val) (control0 : TimeControl p)

local notation "Zplus" =>
  ReferenceFirstLiveRecordingSourceCylinder.SourcePlus
    rate rewards C_star C_h q t s hs control0

private theorem execute_append_one (queue : RecordedQueueRun.Parameters)
    (rounds : List (RecordedQueueRun.RoundInput p.K))
    (round : RecordedQueueRun.RoundInput p.K)
    (state : RecordedQueueRun.RunState p.K) :
    RecordedQueueRun.execute queue (rounds ++ [round]) state =
      RecordedQueueRun.step queue (RecordedQueueRun.execute queue rounds state) round := by
  induction rounds generalizing state with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.cons_append, RecordedQueueRun.execute]
      exact ih (RecordedQueueRun.step queue state head)

private theorem connected_append_one_inv
    {initial final : ReferenceActivePhysicalHorizon.State p rate}
    {rounds : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))}
    {record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)}
    (hconnected : ReferenceActivePhysicalHorizon.Connected initial
      (rounds ++ [record]) final) :
    ReferenceActivePhysicalHorizon.Connected initial rounds record.input.state ∧
      final = record.output.next := by
  induction rounds generalizing initial final with
  | nil =>
      simpa [ReferenceActivePhysicalHorizon.Connected] using hconnected
  | cons head tail ih =>
      rcases hconnected with ⟨hhead, htail⟩
      rcases ih htail with ⟨hprefix, hfinal⟩
      exact ⟨⟨hhead, hprefix⟩, hfinal⟩

private theorem continuing_step_payload_eq
    {input : ReferenceActivePhysicalStep.RoundInput p rate}
    {registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta}
    {owned : CoordinatorLiveServiceFinish.OwnedRegisters registers}
    {base : Fin (p.m - 1) → ℕ}
    {outcome : CoordinatorRoundDispatch.LiveOutcome
      (ReferenceActivePhysicalStep.liveInput input registers owned base)}
    (hcoord : (ReferenceActivePhysicalStep.prepare input).coordinator =
      .live registers owned base outcome)
    (hselected : ∃ selected : ReferenceActivePhysicalStep.Selection input,
      (ReferenceActivePhysicalStep.prepare input).coordinator.selection = some selected)
    (hcontinuing : ∃ dispatched startRoundEq continuation arm,
      outcome = .continuingChosen dispatched startRoundEq continuation arm)
    {nextRegisters : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta}
    {nextOwned : CoordinatorLiveServiceFinish.OwnedRegisters nextRegisters}
    {nextBase : Fin (p.m - 1) → ℕ}
    (hnext : (ReferenceActivePhysicalStep.step input).next.coordinator =
      .live nextRegisters nextOwned nextBase) :
    nextRegisters.payload = registers.payload := by
  rcases hcontinuing with ⟨dispatched, startRoundEq, continuation, arm, houtcome⟩
  subst outcome
  rcases hselected with ⟨selected, hselected⟩
  have hselectedLive :
      (ReferenceActivePhysicalStep.DispatchCut.live registers owned base
        (.continuingChosen dispatched startRoundEq continuation arm)).selection =
        some selected := by
    simpa only [hcoord] using hselected
  have hobserve := ReferenceActivePhysicalStep.observeCoordinator_live_equation
    (ReferenceActivePhysicalStep.prepare input) registers owned base
    (.continuingChosen dispatched startRoundEq continuation arm) hcoord
  have hobserve' :
      (ReferenceActivePhysicalStep.prepare input).observeCoordinator =
        ReferenceActivePhysicalStep.livePostChoice
          (ReferenceActivePhysicalStep.prepare input)
          (ReferenceActivePhysicalStep.liveRegistersAt registers input.time)
          (ReferenceActivePhysicalStep.liveOwnedAt registers owned input.time)
          base dispatched.startResult := by
    simpa [hselectedLive] using hobserve
  have hconfiguration :
      (ReferenceActivePhysicalStep.prepare input).observeCoordinator.configuration =
        .live nextRegisters nextOwned nextBase := by
    calc
      (ReferenceActivePhysicalStep.prepare input).observeCoordinator.configuration =
          (ReferenceActivePhysicalStep.step input).next.coordinator :=
        (ReferenceActivePhysicalStep.step_next_fields input).1.symm
      _ = .live nextRegisters nextOwned nextBase := hnext
  have hstored :
      ReferenceAssignmentPayloadPersistence.storedPayload
        (ReferenceActivePhysicalStep.livePostChoice
          (ReferenceActivePhysicalStep.prepare input)
          (ReferenceActivePhysicalStep.liveRegistersAt registers input.time)
          (ReferenceActivePhysicalStep.liveOwnedAt registers owned input.time)
          base dispatched.startResult).configuration = some nextRegisters.payload := by
    calc
      _ = ReferenceAssignmentPayloadPersistence.storedPayload
          ((ReferenceActivePhysicalStep.prepare input).observeCoordinator.configuration) := by
            rw [← hobserve']
      _ = ReferenceAssignmentPayloadPersistence.storedPayload
          ((ReferenceActivePhysicalStep.step input).next.coordinator) := by
            rw [(ReferenceActivePhysicalStep.step_next_fields input).1]
      _ = some nextRegisters.payload := by rw [hnext]; rfl
  have hframe := ReferenceAssignmentPayloadPersistence.livePostChoice_payload_frame
    (ReferenceActivePhysicalStep.prepare input)
    (ReferenceActivePhysicalStep.liveRegistersAt registers input.time)
    (ReferenceActivePhysicalStep.liveOwnedAt registers owned input.time)
    base dispatched.startResult
  rcases hframe with hnone | hsome
  · rw [hnone] at hstored
    cases hstored
  · have hpayload : some nextRegisters.payload = some registers.payload := by
      simpa only [ReferenceActivePhysicalStep.liveRegistersAt] using hstored.symm.trans hsome
    exact Option.some.inj hpayload

/-- The actual update at the current calendar coordinate of C's original
source. The queue states are runs on the same complete list of actual cells;
the last input is identified by C's `cells_current` theorem. -/
theorem actual_current_stopped_update (z : Zplus) :
    let n := t.val - s
    let cells := ReferenceFirstLiveSourceCellReadout.cells
      rate rewards C_star C_h q t s hs control0 z
    let cell := ReferenceFirstLiveSourceCellReadout.cell
      rate rewards C_star C_h q t s hs control0 z
    let queue := ReferenceFirstLaunchNumericalCell.queueParameters rate
    let past := RecordedQueueRun.run queue (cells.take n)
    let post := RecordedQueueRun.run queue (cells.take (n + 1))
    let κ := UnstoppedRecordedQueueComparison.firstOverflowPrefix queue cells
    (past.overflow = false ↔ n < κ) ∧
    post = RecordedQueueRun.step queue past cell.input ∧
    cell.input.enabled = true ∧
    (∀ j : Fin p.K,
      RecordedQueueRun.acceptedRecord queue past cell.input j =
        if n < κ then
          (true, RecordedQueueRun.quantizedArrival queue cell.input j)
        else (false, 0)) ∧
    (∀ j : Fin p.K,
      post.registers j = QueueReplay.transition (4 * rate.n) (past.registers j)
        (RecordedQueueRun.acceptedRecord queue past cell.input j)) ∧
    (∀ j : Fin p.K,
      post.records j = past.records j ++
        [RecordedQueueRun.acceptedRecord queue past cell.input j]) ∧
    (∀ j : Fin p.K, n < κ →
      post.registers j =
        ((past.registers j).1 + min (4 * rate.n)
            ((past.registers j).2 + RecordedQueueRun.quantizedArrival queue cell.input j),
          (past.registers j).2 + RecordedQueueRun.quantizedArrival queue cell.input j -
            min (4 * rate.n)
              ((past.registers j).2 + RecordedQueueRun.quantizedArrival queue cell.input j))) ∧
    (post.overflow = true ↔
      ∃ j : Fin p.K, 32 * (post.registers j).2 > D p) ∧
    (κ = n + 1 → post.overflow = true) ∧
    (κ ≤ n → ∀ j : Fin p.K,
      post.registers j = past.registers j ∧
      RecordedQueueRun.acceptedRecord queue past cell.input j = (false, 0)) := by
  classical
  intro n cells cell queue past post κ
  have hlength : cells.length = n + 1 := by
    simpa [cells, n, ReferenceFirstLiveSourceCellReadout.cells,
      ReferenceFirstLiveSourceCellReadout.sourceCurrentCount] using
      ReferenceFirstLiveSourceCellReadout.cells_length
        rate rewards C_star C_h q t s hs control0 z
  have hn : n < cells.length := by rw [hlength]; omega
  have hcurrent : cells[n]'hn = cell.input := by
    simpa only [cells, cell, n] using
      (ReferenceFirstLiveSourceCellReadout.cells_current
        rate rewards C_star C_h q t s hs control0 z)
  have htake : cells.take (n + 1) = cells.take n ++ [cell.input] := by
    rw [← List.take_append_getElem hn]
    rw [hcurrent]
  have hpost : post = RecordedQueueRun.step queue past cell.input := by
    dsimp only [post, past, RecordedQueueRun.run]
    rw [htake, execute_append_one]
  have hpastOverflow :=
    UnstoppedRecordedQueueComparison.prefix_overflow_iff_first_overflow_prefix_le
      queue cells n (by omega)
  have hpastNoOverflow : past.overflow = false ↔ n < κ := by
    constructor
    · intro hfalse
      by_contra hnκ
      have hκn : κ ≤ n := Nat.le_of_not_gt hnκ
      have htrue := hpastOverflow.mpr hκn
      simp [past, hfalse] at htrue
    · intro hnκ
      cases hflag : past.overflow with
      | false => rfl
      | true =>
          have hκn := hpastOverflow.mp hflag
          omega
  have henabled : cell.input.enabled = true := by
    simpa only [cell] using
      (ReferenceFirstLiveSourceCellReadout.source_current_cell_fields
        rate rewards C_star C_h q t s hs control0 z).1
  have haccepted (j : Fin p.K) :
      RecordedQueueRun.acceptedRecord queue past cell.input j =
        if n < κ then
          (true, RecordedQueueRun.quantizedArrival queue cell.input j)
        else (false, 0) := by
    by_cases hnκ : n < κ
    · have hflag : past.overflow = false := hpastNoOverflow.mpr hnκ
      simp [RecordedQueueRun.acceptedRecord, hflag, henabled, hnκ]
    · have hκn : κ ≤ n := Nat.le_of_not_gt hnκ
      have hflag : past.overflow = true := hpastOverflow.mpr hκn
      simp [RecordedQueueRun.acceptedRecord, hflag, hnκ]
  have hpostOverflow :=
    UnstoppedRecordedQueueComparison.prefix_overflow_iff_first_overflow_prefix_le
      queue cells (n + 1) (by omega)
  have htransition (j : Fin p.K) :
      post.registers j = QueueReplay.transition (4 * rate.n) (past.registers j)
        (RecordedQueueRun.acceptedRecord queue past cell.input j) := by
    rw [hpost]
    simp [RecordedQueueRun.step, queue,
      ReferenceFirstLaunchNumericalCell.queueParameters]
  have hrecords (j : Fin p.K) :
      post.records j = past.records j ++
        [RecordedQueueRun.acceptedRecord queue past cell.input j] := by
    rw [hpost]
    rfl
  have hservice (j : Fin p.K) (hnκ : n < κ) :
      post.registers j =
        ((past.registers j).1 + min (4 * rate.n)
            ((past.registers j).2 + RecordedQueueRun.quantizedArrival queue cell.input j),
          (past.registers j).2 + RecordedQueueRun.quantizedArrival queue cell.input j -
            min (4 * rate.n)
              ((past.registers j).2 + RecordedQueueRun.quantizedArrival queue cell.input j)) := by
    rw [htransition j, haccepted j]
    simp [hnκ, QueueReplay.transition,
      queue, ReferenceFirstLaunchNumericalCell.queueParameters]
  have hpostCutoff : post.overflow = true ↔ κ ≤ n + 1 := by
    simpa only [post, κ] using hpostOverflow
  have hpostBacklog : post.overflow = true ↔
      ∃ j : Fin p.K, 32 * (post.registers j).2 > D p := by
    simpa [post, queue, ReferenceFirstLaunchNumericalCell.queueParameters] using
      RecordedQueueRun.run_overflow_iff_cutoff queue (cells.take (n + 1))
  refine ⟨hpastNoOverflow, hpost, henabled, haccepted, htransition, hrecords, hservice,
    hpostBacklog, ?_, ?_⟩
  · intro hk
    exact hpostCutoff.mpr (by omega)
  · intro hκn j
    have hflag : past.overflow = true := hpastOverflow.mpr hκn
    have hpres := RecordedQueueRun.step_after_overflow_preserves queue past cell.input hflag j
    have hacc := haccepted j
    have hnot : ¬ n < κ := Nat.not_lt_of_ge hκn
    rw [ite_eq_right hnot] at hacc
    exact ⟨by simpa only [hpost] using hpres.1, hacc⟩

/-- On M's original-source follower subtype, the accepted integer current
arrival is exactly the saved readout before overflow and zero after it. The
second conjunct keeps C's literal original-record `logEmission` identity. -/
theorem actual_current_accepted_saved_readout (i : Fin (p.m - 1))
    (z : ReferenceFirstLiveSourceSavedMoments.SourceFollower
      rate rewards C_star C_h q t s hs control0 i) :
    let zp := ReferenceFirstLiveSourceCellReadout.followerAsSourcePlus
      rate rewards C_star C_h q t s hs control0 i z
    let x := (ReferenceFirstLiveSourceSavedMoments.followerSourceSplit
      rate rewards C_star C_h q t s hs control0 i z).1
    let arm := ReferenceFirstLiveSourceSavedMoments.assignedArm
      rate rewards C_star C_h q t s hs control0 i x
    let queue := ReferenceFirstLaunchNumericalCell.queueParameters rate
    let cells := ReferenceFirstLiveSourceCellReadout.cells
      rate rewards C_star C_h q t s hs control0 zp
    let n := t.val - s
    let past := RecordedQueueRun.run queue (cells.take n)
    let κ := UnstoppedRecordedQueueComparison.firstOverflowPrefix queue cells
    ((RecordedQueueRun.acceptedArrival
        (RecordedQueueRun.acceptedRecord queue past
          (ReferenceFirstLiveSourceCellReadout.cell
            rate rewards C_star C_h q t s hs control0 zp).input arm) : ℝ) /
        (rate.eta.val * (D p : ℝ))) =
      (if n < κ then
        ReferenceFirstLiveSourceSavedMoments.sourceSaved
          rate rewards C_star C_h q t s hs control0 i z
      else (0 : ℝ)) ∧
    RecordedQueueRun.quantizedArrival queue
        (ReferenceFirstLiveSourceCellReadout.cell
          rate rewards C_star C_h q t s hs control0 zp).input arm =
      SparseCalendarReplay.sparseBufferContribution (p.m - 1) (D p : ℝ)
        rate.eta.val
        ((ReferenceFirstLiveSourceSavedMoments.selectedBaselinePayload
          rate rewards C_star C_h q t s hs control0 i x).exponent arm)
        arm (t.val + 1)
        (ReferenceFollowerBufferProvenance.logEmission i
          (ReferenceFirstLiveRecordingSourceCylinder.originalCurrentRecord
            rate rewards C_star C_h q t s hs control0 z.val)) := by
  classical
  intro zp x arm queue cells n past κ
  have hqueue := actual_current_stopped_update rate rewards C_star C_h q t s hs control0 zp
  rcases hqueue with ⟨hpast, _, _, haccepted, _, _, _, _, _, _⟩
  have hsaved :=
    ReferenceFirstLiveSourceCellReadout.source_current_normalized_arrival_eq_source_saved
      rate rewards C_star C_h q t s hs control0 i z
  have hlog :=
    ReferenceFirstLiveSourceCellReadout.source_current_arrival_eq_log_emission
      rate rewards C_star C_h q t s hs control0 i z
  constructor
  · by_cases hnκ : n < κ
    · have hrecord := haccepted arm
      rw [ite_eq_left hnκ] at hrecord
      have harrival :
          RecordedQueueRun.acceptedArrival
            (RecordedQueueRun.acceptedRecord queue past
              (ReferenceFirstLiveSourceCellReadout.cell
                rate rewards C_star C_h q t s hs control0 zp).input arm) =
            RecordedQueueRun.quantizedArrival queue
              (ReferenceFirstLiveSourceCellReadout.cell
                rate rewards C_star C_h q t s hs control0 zp).input arm := by
        rw [hrecord]
        rfl
      calc
        _ = ((RecordedQueueRun.quantizedArrival queue
            (ReferenceFirstLiveSourceCellReadout.cell
              rate rewards C_star C_h q t s hs control0 zp).input arm : ℕ) : ℝ) /
              (rate.eta.val * (D p : ℝ)) := by rw [harrival]
        _ = ReferenceFirstLiveSourceSavedMoments.sourceSaved
            rate rewards C_star C_h q t s hs control0 i z := by
          simpa only [zp, x, arm, queue, cells, n, κ] using hsaved
        _ = if n < κ then
              ReferenceFirstLiveSourceSavedMoments.sourceSaved
                rate rewards C_star C_h q t s hs control0 i z else 0 := by simp [hnκ]
    · have hrecord := haccepted arm
      have hnot : ¬ n < κ := by omega
      rw [ite_eq_right hnot] at hrecord
      rw [ite_eq_right hnot]
      rw [hrecord]
      simp [RecordedQueueRun.acceptedArrival]
  · simpa only [zp, x, arm, queue] using hlog

/-- The physical run made by N still executes the current source record and
ends at that record's actual output, irrespective of the numerical stop. -/
theorem actual_current_run_endpoint (z : Zplus) :
    let E := ReferenceFirstWindowNumericalStream.actualFirstLiveRun
      rate z.val.val rewards C_star C_h z.val.property.2.1
      (ReferenceFirstLiveSourceCellReadout.sourceCurrentCount t s)
      (ReferenceFirstLiveSourceCellReadout.source_current_span
        rate rewards C_star C_h q t s hs control0 z)
    E.finalState =
      (ReferenceFirstLiveRecordingSourceCylinder.originalCurrentRecord
        rate rewards C_star C_h q t s hs control0 z.val).output.next := by
  classical
  intro E
  let n := t.val - s
  let original := ReferenceFirstLiveRecordingSourceCylinder.originalCurrentRecord
    rate rewards C_star C_h q t s hs control0 z.val
  have hlength : E.records.length = n + 1 := by
    have h := ReferenceActivePhysicalHorizon.run_record_count
      (ReferenceFirstLaunchNumericalCell.launchState
        rate z.val.val rewards C_star C_h z.val.property.2.1)
      z.val.val.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z.val.val)
      rewards
      (ReferenceInitializationRun.elapsed p
        (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput
            z.val.val rewards C_star C_h rate)).completed)
      (ReferenceFirstLiveSourceCellReadout.sourceCurrentCount t s)
      (ReferenceFirstLiveSourceCellReadout.source_current_span
        rate rewards C_star C_h q t s hs control0 z)
      (ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
        rate z.val.val rewards C_star C_h z.val.property.2.1).activeAtStart
    simpa [E, n, ReferenceFirstWindowNumericalStream.actualFirstLiveRun,
      ReferenceFirstLiveSourceCellReadout.sourceCurrentCount] using h
  have hindex : n < E.records.length := by rw [hlength]; omega
  have hrecord : E.records[n]'hindex = original := by
    have hwindow := ReferenceFirstLiveSourceCellReadout.source_current_record
      rate rewards C_star C_h q t s hs control0 z
    have hwindowEq :
        ReferenceFirstLiveSourceCellReadout.sourceCurrentWindow
          rate rewards C_star C_h q t s hs control0 z = E.records := by
      simpa [ReferenceFirstLiveSourceCellReadout.sourceCurrentWindow,
        ReferenceFirstLiveSourceCellReadout.sourceCurrentCount, E] using
        (ReferenceFirstLiveSourceCellReadout.source_current_window
          rate rewards C_star C_h q t s hs control0 z).1
    simpa only [hwindowEq,
        ReferenceFirstLiveSourceCellReadout.source_current_index_val] using hwindow
  have hrecords : E.records = E.records.take n ++ [original] := by
    calc
      E.records = E.records.take (n + 1) := by
        symm
        exact List.take_of_length_le (by rw [hlength])
      _ = E.records.take n ++ [E.records[n]] := by
        rw [← List.take_append_getElem hindex]
      _ = E.records.take n ++ [original] := by rw [hrecord]
  let initial := ReferenceFirstLaunchNumericalCell.launchState
    rate z.val.val rewards C_star C_h z.val.property.2.1
  let elapsed := ReferenceInitializationRun.elapsed p
    (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z.val.val rewards C_star C_h rate)).completed
  let count := ReferenceFirstLiveSourceCellReadout.sourceCurrentCount t s
  let hspan := ReferenceFirstLiveSourceCellReadout.source_current_span
    rate rewards C_star C_h q t s hs control0 z
  let seed := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
    rate z.val.val rewards C_star C_h z.val.property.2.1
  have hconnected : ReferenceActivePhysicalHorizon.Connected initial E.records E.finalState := by
    simpa only [E, ReferenceFirstWindowNumericalStream.actualFirstLiveRun] using
      ReferenceActivePhysicalHorizon.run_connected initial z.val.val.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p z.val.val)
        rewards elapsed count hspan seed.activeAtStart
  rw [hrecords] at hconnected
  exact (connected_append_one_inv rate hconnected).2

/-- Before the first overflow, the numerical current update, the current
original-source record, and the physical post-round boundary are the same
chronological endpoint. Every conditional physical witness is produced from
the actual C window and S's proved boundary comparison. -/
theorem actual_current_stopped_physical_endpoint (z : Zplus) :
    let n := t.val - s
    let count := ReferenceFirstLiveSourceCellReadout.sourceCurrentCount t s
    let span := ReferenceFirstLiveSourceCellReadout.source_current_span
      rate rewards C_star C_h q t s hs control0 z
    let source := z.val.val
    let κ := UnstoppedRecordedQueueComparison.firstOverflowPrefix
      (ReferenceFirstLaunchNumericalCell.queueParameters rate)
      (ReferenceFirstLiveSourceCellReadout.cells
        rate rewards C_star C_h q t s hs control0 z)
    let cell := ReferenceFirstLiveSourceCellReadout.cell
      rate rewards C_star C_h q t s hs control0 z
    let queue := ReferenceFirstLaunchNumericalCell.queueParameters rate
    let cells := ReferenceFirstLiveSourceCellReadout.cells
      rate rewards C_star C_h q t s hs control0 z
    let past := RecordedQueueRun.run queue (cells.take n)
    let post := RecordedQueueRun.run queue (cells.take (n + 1))
    let E := ReferenceFirstWindowNumericalStream.actualFirstLiveRun
      rate source rewards C_star C_h z.val.property.2.1 count span
    (past.overflow = false ↔ n < κ) ∧
    post = RecordedQueueRun.step queue past cell.input ∧
    cell.input.enabled = true ∧
    (∀ j : Fin p.K,
      RecordedQueueRun.acceptedRecord queue past cell.input j =
        if n < κ then (true, RecordedQueueRun.quantizedArrival queue cell.input j)
        else (false, 0)) ∧
    (n < κ →
      ∃ hprefix : ReferenceInitializationRun.elapsed p
        (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
          + (n + 1) ≤ p.T,
      ∃ boundary : ReferenceActivePhysicalHorizon.Run
        (ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h
          z.val.property.2.1),
      boundary = ReferenceActivePhysicalHorizon.run
        (ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h
          z.val.property.2.1)
        source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
        (ReferenceInitializationRun.elapsed p
          (ReferenceInitializationRun.output
            (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed)
        (n + 1) hprefix
        (ReferenceFirstWindowNumericalStream.actualFirstLiveSeed rate source rewards C_star C_h
          z.val.property.2.1).activeAtStart ∧
      ∃ r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta,
      ∃ owned : CoordinatorLiveServiceFinish.OwnedRegisters r,
      ∃ base : Fin (p.m - 1) → ℕ,
        E.finalState = boundary.finalState ∧
        E.finalState =
          (ReferenceFirstLiveRecordingSourceCylinder.originalCurrentRecord
            rate rewards C_star C_h q t s hs control0 z.val).output.next ∧
        boundary.finalState.coordinator = .live r owned base ∧
        r.payload.sigma.val = s ∧ r.payload.n = rate.n ∧
        (∀ i, base i = 0) ∧
        (ReferenceFirstLiveSourceCellReadout.cell
          rate rewards C_star C_h q t s hs control0 z).selected.view.payload = r.payload ∧
        (∃ birth : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate),
          birth ∈ E.records ∧
          ReferenceAssignmentPayloadPersistence.InstallationBirth birth r.payload ∧
          birth.input.time.val = s) ∧
        (∀ a : CanonicalFastSampling.FastArm r.payload.slowSet,
          (r.complementScores a, owned.queue a) = post.registers a.1 ∧
          owned.previousService a = (post.registers a.1).1 - (past.registers a.1).1) ∧
        (∀ i : Fin (p.m - 1),
          ∃ sb mb, E.finalState.followers i = .ordinary sb mb ∧
            ((sb.status ≠ .unoccupied →
              sb.lastDown = some (r.payload.downRecord i) ∧
              (sb.S, sb.backlog) = post.registers (r.payload.assignment.assigned i) ∧
              sb.delta = (post.registers (r.payload.assignment.assigned i)).1 -
                (past.registers (r.payload.assignment.assigned i)).1 ∧
              ∃ j : Fin (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
                  rate source rewards C_star C_h z.val.property.2.1 count span).length,
                j.val < n + 1 ∧
                ReferenceAcceptedUpFollowerHistory.RetainedDown
                  (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
                    rate source rewards C_star C_h z.val.property.2.1 count span)[j.val]
                  i (r.payload.downRecord i)) ∧
             (sb.status = .unoccupied →
              sb.lastDown = none ∧ sb.S = 0 ∧ sb.delta = 0 ∧ sb.backlog = 0 ∧
              sb.buffer =
                ((ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
                  rate source rewards C_star C_h z.val.property.2.1).followers i).buffer ++
                (E.records.take (n + 1)).flatMap
                  (ReferenceFollowerBufferProvenance.logEmission i) ∧
              ReferenceFirstAcceptedUpNumericSnapshot.firstReplyQueueRecords
                E.records i (n + 1) (r.payload.downRecord i) (n + 1) =
                ((cells.take (n + 1)).map fun c =>
                  (c.enabled, RecordedQueueRun.quantizedArrival queue c
                    (r.payload.assignment.assigned i))) ∧
              QueueReplay.replay (4 * rate.n) (0, 0)
                (ReferenceFirstAcceptedUpNumericSnapshot.firstReplyQueueRecords
                  E.records i (n + 1) (r.payload.downRecord i) (n + 1)) =
                post.registers (r.payload.assignment.assigned i))))) := by
  classical
  intro n count span source κ cell queue cells past post E
  have hcount : count = n + 1 := by
    rfl
  have hcellsSource : cells =
      ReferenceFirstWindowNumericalStream.actualLiveSourceCells rate source rewards C_star C_h
        z.val.property.2.1 count span := by
    rfl
  have hqueue := actual_current_stopped_update
    rate rewards C_star C_h q t s hs control0 z
  rcases hqueue with ⟨hpast, hstep, henabled, haccepted, _, _, _, _, _, _⟩
  have hwindowLength := ReferenceFirstLiveSourceCellReadout.source_current_window_length
    rate rewards C_star C_h q t s hs control0 z
  have hb : n + 1 ≤
      (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
        rate source rewards C_star C_h z.val.property.2.1 count span).length := by
    have hlen :
        (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
          rate source rewards C_star C_h z.val.property.2.1 count span).length = n + 1 := by
      simpa [ReferenceFirstLiveSourceCellReadout.sourceCurrentWindow,
        ReferenceFirstLiveSourceCellReadout.sourceCurrentCount, source, count, hcount] using
        hwindowLength
    rw [hlen]
  have hS :=
    ReferenceFirstLiveStoppedQueueComparison.actual_first_live_stopped_queue_common_boundary
      rate source rewards C_star C_h z.val.property.2.1 count span (n + 1) hb
  dsimp only at hS
  rcases hS with ⟨hspanS, hsourceReplay, hstopAtB, hoverflow, hphysical, _⟩
  refine ⟨hpast, hstep, henabled, haccepted, ?_⟩
  intro hnκ
  have hbκ : n + 1 ≤ κ := by omega
  rcases hphysical hbκ with ⟨hprefix, _hzero, hpositive⟩
  rcases hpositive (by omega) with
    ⟨r, owned, base, hLive, hsigma, hrate, hbase, hbirth, hcomplement,
      hfollowers, _hpartition, _hfast⟩
  let initial := ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h
    z.val.property.2.1
  let seed := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed rate source rewards C_star C_h
    z.val.property.2.1
  let boundary := ReferenceActivePhysicalHorizon.run initial source.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
    (ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed)
    (n + 1) hprefix seed.activeAtStart
  have hboundaryEq : boundary = E := by
    dsimp [boundary, E, initial, seed,
      ReferenceFirstWindowNumericalStream.actualFirstLiveRun,
      ReferenceFirstWindowNumericalStream.actualFirstLiveSeed]
    congr 1
  have hboundaryStates := congrArg
    (fun run : ReferenceActivePhysicalHorizon.Run initial => run.finalState) hboundaryEq
  have hendpoint := actual_current_run_endpoint
    rate rewards C_star C_h q t s hs control0 z
  have hendpoint' : E.finalState =
      (ReferenceFirstLiveRecordingSourceCylinder.originalCurrentRecord
        rate rewards C_star C_h q t s hs control0 z.val).output.next := by
    simpa [E, ReferenceFirstLiveSourceCellReadout.sourceCurrentCount, count] using hendpoint
  have hbaseEndpoint : E.finalState.coordinator = .live r owned base := by
    calc
      E.finalState.coordinator = boundary.finalState.coordinator := by
        exact congrArg (fun st : ReferenceActivePhysicalHorizon.State p rate => st.coordinator)
          hboundaryStates.symm
      _ = .live r owned base := hLive
  let split := ReferenceFirstLiveRecordingSourceCylinder.branchSourceSplit
    rate rewards C_star C_h q t s hs control0 z
  obtain ⟨statesC, memoriesC, rC, ownedC, baseC, dC, hsStartC, cC, armC,
      hcoordC, _hordinaryC, hbasePayloadC, _hselectedRecord, _hvalidC, _hsourceMarkerC⟩ :=
    ReferenceFirstLiveRecordingSourceCylinder.sourceMarker_eq_sourceArm
      rate rewards C_star C_h q t s hs control0 z
  have hcontrolsC := ReferenceContinuingLiveSlicePreparation.continuing_cut_at_control
    (ReferenceFirstLiveRecordingReadoutMeasurability.sourceCurrentInput split.1.val)
    rC ownedC baseC dC hsStartC cC armC hcoordC
  rcases hcontrolsC split.2 with ⟨currentControl, currentArm, hcoordAtCurrent⟩
  let original := ReferenceFirstLiveRecordingSourceCylinder.originalCurrentRecord
    rate rewards C_star C_h q t s hs control0 z.val
  have hinputCurrent :
      ReferenceFirstLiveRecordingReadoutMeasurability.sourceInputAtControl
        split.1.val split.2 = original.input := by
    simpa [split, ReferenceFirstLiveRecordingSourceCylinder.branchSourceSplit, original] using
      (ReferenceFirstLiveRecordingSourceCylinder.sourceInputAtControl_eq_original
        rate rewards C_star C_h q t s hs control0 z.val)
  let currentInput :=
    ReferenceFirstLiveRecordingReadoutMeasurability.sourceInputAtControl
      split.1.val split.2
  have hcoordAt : (ReferenceActivePhysicalStep.prepare currentInput).coordinator =
      .live rC ownedC baseC (.continuingChosen dC hsStartC currentControl currentArm) := by
    change (ReferenceActivePhysicalStep.prepare
      (ReferenceContinuingLiveSlicePreparation.inputAtControl
        (ReferenceFirstLiveRecordingReadoutMeasurability.sourceCurrentInput split.1.val)
        split.2)).coordinator = _ at hcoordAtCurrent
    exact hcoordAtCurrent
  let selectedCurrent := ReferenceContinuingLiveSlicePreparation.continuingSelection
    currentInput rC ownedC baseC dC hsStartC currentControl currentArm
  have hselectedCurrent :=
    ReferenceContinuingLiveSlicePreparation.continuingSelection_eq_actual
      currentInput rC ownedC baseC dC hsStartC currentControl currentArm hcoordAt
  have hnext : (ReferenceActivePhysicalStep.step original.input).next.coordinator =
      .live r owned base := by
    calc
      (ReferenceActivePhysicalStep.step original.input).next.coordinator =
          original.output.next.coordinator := rfl
      _ = E.finalState.coordinator := congrArg
        (fun st : ReferenceActivePhysicalHorizon.State p rate => st.coordinator) hendpoint'.symm
      _ = boundary.finalState.coordinator := congrArg
        (fun st : ReferenceActivePhysicalHorizon.State p rate => st.coordinator)
        (congrArg (fun run : ReferenceActivePhysicalHorizon.Run initial => run.finalState)
          hboundaryEq).symm
      _ = .live r owned base := hLive
  have hnextCurrent : (ReferenceActivePhysicalStep.step currentInput).next.coordinator =
      .live r owned base := by
    calc
      (ReferenceActivePhysicalStep.step currentInput).next.coordinator =
          (ReferenceActivePhysicalStep.step original.input).next.coordinator :=
        congrArg (fun input => (ReferenceActivePhysicalStep.step input).next.coordinator)
          hinputCurrent
      _ = .live r owned base := hnext
  have hpayloadPersists := continuing_step_payload_eq
    rate (input := currentInput) hcoordAt ⟨selectedCurrent, hselectedCurrent⟩
    ⟨dC, hsStartC, currentControl, currentArm, rfl⟩ hnextCurrent
  have hcellPayload := ReferenceFirstLiveSourceCellReadout.source_current_cell_payload
    rate rewards C_star C_h q t s hs control0 z
  have hselectedPayload :
      (ReferenceFirstLiveSourceCellReadout.cell
        rate rewards C_star C_h q t s hs control0 z).selected.view.payload = r.payload :=
    hcellPayload.trans (hbasePayloadC.trans hpayloadPersists.symm)
  have hElapsed := ReferenceFirstLiveSourceCellReadout.source_current_elapsed_eq
    rate rewards C_star C_h q t s hs control0 z
  have hpostReplay (a : Fin p.K) :
      post.registers a = UnstoppedRecordedQueueComparison.unstoppedReplay
        queue cells (n + 1) a := by
    have h := UnstoppedRecordedQueueComparison.prefix_registers_eq_unstopped_replay
      queue cells (n + 1) (by
        have hlen := ReferenceFirstLiveSourceCellReadout.cells_length
          rate rewards C_star C_h q t s hs control0 z
        dsimp [cells, n, ReferenceFirstLiveSourceCellReadout.cells,
          ReferenceFirstLiveSourceCellReadout.sourceCurrentCount] at hlen ⊢
        omega) a
    have hminBound : n + 1 ≤
        UnstoppedRecordedQueueComparison.firstOverflowPrefix queue cells := by
      simpa only [κ, queue, ← hcellsSource] using Nat.succ_le_of_lt hnκ
    have hmin : min (n + 1)
        (UnstoppedRecordedQueueComparison.firstOverflowPrefix queue cells) = n + 1 :=
      Nat.min_eq_left hminBound
    simpa only [post, hmin] using h
  have hpastReplay (a : Fin p.K) :
      past.registers a = UnstoppedRecordedQueueComparison.unstoppedReplay
        queue cells n a := by
    have h := UnstoppedRecordedQueueComparison.prefix_registers_eq_unstopped_replay
      queue cells n (by
        have hlen := ReferenceFirstLiveSourceCellReadout.cells_length
          rate rewards C_star C_h q t s hs control0 z
        dsimp [cells, n, ReferenceFirstLiveSourceCellReadout.cells,
          ReferenceFirstLiveSourceCellReadout.sourceCurrentCount] at hlen ⊢
        omega) a
    have hminBound : n ≤
        UnstoppedRecordedQueueComparison.firstOverflowPrefix queue cells := by
      simpa only [κ, queue, ← hcellsSource] using Nat.le_of_lt hnκ
    have hmin : min n
        (UnstoppedRecordedQueueComparison.firstOverflowPrefix queue cells) = n :=
      Nat.min_eq_left hminBound
    simpa only [past, hmin] using h
  have hdeltaReplay (a : Fin p.K) :
      (UnstoppedRecordedQueueComparison.unstoppedReplay queue cells (n + 1) a).1 -
        (UnstoppedRecordedQueueComparison.unstoppedReplay queue cells n a).1 =
      (post.registers a).1 - (past.registers a).1 := by
    rw [← hpostReplay a, ← hpastReplay a]
  have hpreviousIndex : (t.val - s + 1) - 1 = t.val - s := by omega
  have hbirthTime (birth : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
      (htime : birth.input.time.val =
        ReferenceInitializationRun.elapsed p
          (ReferenceInitializationRun.output
            (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed) :
      birth.input.time.val = s := by
    calc
      birth.input.time.val =
          ReferenceInitializationRun.elapsed p
            (ReferenceInitializationRun.output
              (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed := htime
      _ = ReferenceFirstLiveSourceCellReadout.sourceCurrentElapsed
          rate rewards C_star C_h q t s hs control0 z := rfl
      _ = s := hElapsed
  refine ⟨hprefix, boundary, rfl, ?_⟩
  refine ⟨r, owned, base, ?_, hendpoint', hLive, ?_, hrate, hbase,
    hselectedPayload, ?_, ?_, ?_⟩
  · exact hboundaryStates.symm
  · calc
      r.payload.sigma.val =
          ReferenceInitializationRun.elapsed p
            (ReferenceInitializationRun.output
              (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed := hsigma
      _ = ReferenceFirstLiveSourceCellReadout.sourceCurrentElapsed
          rate rewards C_star C_h q t s hs control0 z := rfl
      _ = s := hElapsed
  · rcases hbirth with ⟨birth, hbirthMem, hbirthInst, hbirthAt⟩
    have hbirthMemB : birth ∈ boundary.records := by
      simpa [boundary] using hbirthMem
    rw [hboundaryEq] at hbirthMemB
    have hbirthMemE : birth ∈ E.records := hbirthMemB
    exact ⟨birth, hbirthMemE, hbirthInst,
      hbirthTime birth hbirthAt⟩
  · intro a
    rcases hcomplement a with ⟨hregs, hprev⟩
    refine ⟨?_, ?_⟩
    · simpa only [post, ← hcellsSource] using hregs
    · calc
        owned.previousService a =
            (UnstoppedRecordedQueueComparison.unstoppedReplay queue cells (n + 1) a.1).1 -
              (UnstoppedRecordedQueueComparison.unstoppedReplay queue cells n a.1).1 := by
          simpa only [n, queue, ← hcellsSource, hpreviousIndex] using hprev
        _ = (post.registers a.1).1 - (past.registers a.1).1 := hdeltaReplay a.1
  · intro i
    rcases hfollowers i with ⟨sb, mb, hstate, hoccupied, hunoccupied⟩
    have hstateB : boundary.finalState.followers i = .ordinary sb mb := by
      simpa [boundary] using hstate
    have hstateE : E.finalState.followers i = .ordinary sb mb := by
      simpa only [hboundaryStates] using hstateB
    refine ⟨sb, mb, hstateE, ?_, ?_⟩
    · intro hocc
      rcases hoccupied hocc with ⟨hlast, hregs, hdelta, hretained⟩
      have hregsPost : (sb.S, sb.backlog) = post.registers
          (r.payload.assignment.assigned i) := by
        simpa only [post, ← hcellsSource] using hregs
      have hdeltaPost : sb.delta =
          (post.registers (r.payload.assignment.assigned i)).1 -
            (past.registers (r.payload.assignment.assigned i)).1 := by
        calc
          sb.delta =
              (UnstoppedRecordedQueueComparison.unstoppedReplay queue cells (n + 1)
                (r.payload.assignment.assigned i)).1 -
              (UnstoppedRecordedQueueComparison.unstoppedReplay queue cells n
                (r.payload.assignment.assigned i)).1 := by
            simpa only [n, queue, ← hcellsSource, hpreviousIndex] using hdelta
          _ = _ := hdeltaReplay (r.payload.assignment.assigned i)
      exact ⟨by simpa only [hboundaryStates] using hlast, hregsPost, hdeltaPost,
        hretained⟩
    · intro hunocc
      rcases hunoccupied hunocc with
        ⟨hlast, hS, hdelta, hbacklog, hbuffer, hreply⟩
      rcases hreply with ⟨hreplyRecords, hvirtual⟩
      have hvirtualPost :
          QueueReplay.replay (4 * rate.n) (0, 0)
            (ReferenceFirstAcceptedUpNumericSnapshot.firstReplyQueueRecords
              E.records i (n + 1) (r.payload.downRecord i) (n + 1)) =
          post.registers (r.payload.assignment.assigned i) := by
        calc
          _ = UnstoppedRecordedQueueComparison.unstoppedReplay queue cells (n + 1)
              (r.payload.assignment.assigned i) := by
            simpa only [n, E, ← hcellsSource] using hvirtual
          _ = _ := (hpostReplay (r.payload.assignment.assigned i)).symm
      exact ⟨by simpa only [hboundaryStates] using hlast, hS, hdelta, hbacklog,
        by simpa [E] using hbuffer,
        by simpa only [E, ← hcellsSource] using hreplyRecords, hvirtualPost⟩

end Bandits.Support.ReferenceFirstLiveChronologicalRetainedUpdate

end
