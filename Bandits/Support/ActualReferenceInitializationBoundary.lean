/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ActualReferenceInitializationFold
public import Bandits.Support.ActualInitializationMonitorTrace

import Lean.Elab.Tactic.Omega

/-!
# One actual/reference initialization boundary

Deterministic one-block monitor and handoff comparisons, retaining the
original `SourceInput`, selected true row, rounded reward table, rate, shared
cost constants, reference boundary, actual carry, and prior physical record
accumulator. The current-block restrictions are the accepted generated DOWN
obstruction complement, the literal all-candidate `cleanPrefix` condition,
and the reference's post-pending force condition. These are internal event
inputs, not unconditional coupling claims or manuscript premises.

Sources: `sources/zip4/manuscript/07_public_setup.tex:39-57,63-140` and
`sources/zip4/manuscript/08_main_theorem.tex:29-42,67-83`.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.BootstrapObservedFollower
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.BootstrapCoordinatorLocalRound
open Bandits.Support.BootstrapPhysicalBlock
open Bandits.Support.BootstrapLaunchMonitor
open Bandits.Support.ActiveRoundActions
open Bandits.Support.ActualInitializationRun
open Bandits.Support.ActualInitializationHorizon
open Bandits.Support.ReferenceInitializationRun
open Bandits.Support.ActualReferenceInitializationBlock
open Bandits.Support.ActualReferenceInitializationFold
open Bandits.Support.ActualInitializationMonitorTrace
open scoped BigOperators Classical

namespace Bandits.Support.ActualReferenceInitializationBoundary

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := Bandits.Support.ActiveFollowerDownAcceptance.RateInput

variable {p : Parameters}

private theorem blockTimes_length (block : Fin (n_boot p)) (cursor fuel : ℕ)
    (hlength : cursor + fuel = BootstrapObservedFollower.blockLength p block) :
    (ActualInitializationRun.blockTimes p block cursor fuel hlength).length = fuel := by
  induction fuel generalizing cursor with
  | zero => simp [ActualInitializationRun.blockTimes]
  | succ fuel ih => simp [ActualInitializationRun.blockTimes, ih]

private theorem blockTimes_getElem (block : Fin (n_boot p)) (cursor fuel : ℕ)
    (hlength : cursor + fuel = BootstrapObservedFollower.blockLength p block)
    (j : Fin fuel) :
    (ActualInitializationRun.blockTimes p block cursor fuel hlength)[j.val]'(by
      rw [blockTimes_length]
      exact j.isLt) =
      ActualInitializationRun.blockTime p block (cursor + j.val) (by omega) := by
  induction fuel generalizing cursor with
  | zero => exact Fin.elim0 j
  | succ fuel ih =>
      cases j using Fin.cases with
      | zero => simp [ActualInitializationRun.blockTimes, ActualInitializationRun.blockTime]
      | succ j =>
          have htail := ih (cursor + 1) (by omega) j
          simp only [ActualInitializationRun.blockTimes, Fin.val_succ,
            List.getElem_cons_succ]
          rw [htail]
          apply Fin.ext
          simp only [ActualInitializationRun.blockTime]
          omega

private theorem list_sum_map_eq_fin_sum {α β : Type*} [AddCommMonoid β]
    (xs : List α) (f : α → β) :
    (xs.map f).sum = ∑ j : Fin xs.length, f xs[j.val] := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      rw [Fin.sum_univ_succ]
      simp only [Fin.val_zero, List.getElem_cons_zero, Fin.val_succ,
        List.getElem_cons_succ]
      exact congrArg (fun z => f x + z) ih

private theorem foldBlock_record_time_value
    {rate : RateInput p} {block : Fin (n_boot p)}
    {source : SourceInput p} {rewards : ActualInitializationPhysicalStep.GridRewardTable p}
    {C_star C_h : ℝ}
    (folded : BlockFoldOutput p rate block source rewards C_star C_h 0)
    (j : Fin folded.records.length) :
    (folded.records[j.val]).time.val =
      BootstrapObservedFollower.blockStart p block + j.val := by
  have hlength : 0 + folded.records.length =
      BootstrapObservedFollower.blockLength p block := by
    have h := folded.record_count
    rw [folded.consumed_eq_blockLength] at h
    omega
  have hchron : folded.records.map (fun record => record.time) =
      ActualInitializationRun.blockTimes p block 0 folded.records.length hlength := by
    simpa [ActualInitializationRun.PhysicalRoundRecord.times] using folded.chronological
  have htimeOpt := congrArg (fun ts : List (Fin p.T) => ts[j.val]?) hchron
  have htimeLeft : (folded.records.map fun record => record.time)[j.val]? =
      some folded.records[j.val].time := by
    simp [List.getElem?_map, List.getElem?_eq_getElem j.isLt]
  have htimeRight :
      (ActualInitializationRun.blockTimes p block 0 folded.records.length hlength)[j.val]? =
        some (ActualInitializationRun.blockTime p block j.val (by omega)) := by
    have hj : j.val <
        (ActualInitializationRun.blockTimes p block 0 folded.records.length hlength).length := by
      rw [blockTimes_length]
      exact j.isLt
    rw [List.getElem?_eq_getElem hj]
    simpa using blockTimes_getElem block 0 folded.records.length hlength j
  rw [htimeLeft, htimeRight] at htimeOpt
  have htime : folded.records[j.val].time =
      ActualInitializationRun.blockTime p block j.val (by omega) :=
    Option.some.inj htimeOpt
  simpa [ActualInitializationRun.blockTime] using congrArg Fin.val htime

private theorem foldBlock_record_time_mem
    {rate : RateInput p} {block : Fin (n_boot p)}
    {source : SourceInput p} {rewards : ActualInitializationPhysicalStep.GridRewardTable p}
    {C_star C_h : ℝ}
    (folded : BlockFoldOutput p rate block source rewards C_star C_h 0)
    (j : Fin folded.records.length) :
    (folded.records[j.val]).time ∈ calendarBlock p block := by
  have hval := foldBlock_record_time_value folded j
  have hstop : BootstrapObservedFollower.blockStart p block +
      BootstrapObservedFollower.blockLength p block =
        BootstrapObservedFollower.blockStop p block :=
    ActualInitializationRun.blockStart_add_length_eq_stop p block
  rw [BootstrapDimensions.mem_calendarBlock_iff]
  constructor
  · rw [foldBlock_record_time_value folded j]
    simpa [BootstrapObservedFollower.blockStart] using
      (Nat.le_add_right (BootstrapObservedFollower.blockStart p block) j.val)
  · have hlen : folded.records.length = BootstrapObservedFollower.blockLength p block := by
      have h := folded.record_count
      rw [folded.consumed_eq_blockLength] at h
      omega
    have hjlt : j.val < BootstrapObservedFollower.blockLength p block := by
      rw [← hlen]
      exact j.isLt
    have hlt : (folded.records[j.val]).time.val <
        BootstrapObservedFollower.blockStop p block := by
      rw [hval, ← hstop]
      exact Nat.add_lt_add_left hjlt _
    simpa [BootstrapObservedFollower.blockStop] using hlt

private theorem foldBlock_record_time_surjective
    {rate : RateInput p} {block : Fin (n_boot p)}
    {source : SourceInput p} {rewards : ActualInitializationPhysicalStep.GridRewardTable p}
    {C_star C_h : ℝ}
    (folded : BlockFoldOutput p rate block source rewards C_star C_h 0)
    (t : Fin p.T) (ht : t ∈ calendarBlock p block) :
    ∃ j : Fin folded.records.length, (folded.records[j.val]).time = t := by
  have hlen : folded.records.length = BootstrapObservedFollower.blockLength p block := by
    have h := folded.record_count
    rw [folded.consumed_eq_blockLength] at h
    omega
  have hmem := (BootstrapDimensions.mem_calendarBlock_iff p block t).mp ht
  have hlo : BootstrapObservedFollower.blockStart p block ≤ t.val := by
    simpa [BootstrapObservedFollower.blockStart] using hmem.1
  have hstop : BootstrapObservedFollower.blockStart p block +
      BootstrapObservedFollower.blockLength p block =
        BootstrapObservedFollower.blockStop p block :=
    ActualInitializationRun.blockStart_add_length_eq_stop p block
  have hoff : t.val - BootstrapObservedFollower.blockStart p block <
      BootstrapObservedFollower.blockLength p block := by
    have hlo : BootstrapObservedFollower.blockStart p block ≤ t.val := by
      simpa [BootstrapObservedFollower.blockStart] using hmem.1
    have hhi : t.val < BootstrapObservedFollower.blockStop p block := by
      change t.val < BootstrapObservedFollower.blockStop p block
      exact hmem.2
    rw [← hstop] at hhi
    omega
  let j : Fin folded.records.length := ⟨t.val - BootstrapObservedFollower.blockStart p block,
    by rw [hlen]; exact hoff⟩
  refine ⟨j, ?_⟩
  apply Fin.ext
  rw [foldBlock_record_time_value folded j]
  dsimp [j]
  omega

private theorem recordPositiveDownCredit_eq_referenceCredit
    (source : SourceInput p) (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (rate : RateInput p) (C_star C_h : ℝ) (b : ReferenceInitializationRun.Boundary p)
    (h : b.completed < n_boot p)
    {foldStar foldH : ℝ}
    (folded : BlockFoldOutput p rate (ReferenceInitializationRun.nextBlock b h)
      source rewards foldStar foldH 0)
    (hrecords : ∀ record ∈ folded.records,
      record.result.actions = BootstrapPhysicalBlock.actions
        (ReferenceInitializationRun.physical
          (referenceInput source rewards C_star C_h rate) b h)
        (BootstrapPhysicalBlock.run
          (ReferenceInitializationRun.physical
            (referenceInput source rewards C_star C_h rate) b h) record.time.val)
        record.time ∧
      record.result.feedback = (fun i => BootstrapPhysicalBlock.observationIndex
        (ReferenceInitializationRun.physical
          (referenceInput source rewards C_star C_h rate) b h)
        (BootstrapPhysicalBlock.run
          (ReferenceInitializationRun.physical
            (referenceInput source rewards C_star C_h rate) b h) record.time.val)
        record.time i) ∧
      ∀ i, recordEntry record i = ReferenceInitializationRun.ownEntry
        (ReferenceInitializationRun.physical
          (referenceInput source rewards C_star C_h rate) b h) i record.time)
    (j : Fin folded.records.length) (arm : Fin p.K) :
    recordPositiveDownCredit folded.records[j.val] arm =
      BootstrapLaunchMonitor.creditCounter (fun _ => 0)
        (ReferenceInitializationRun.downArm
          (referenceInput source rewards C_star C_h rate) b h
          folded.records[j.val].time) arm := by
  let x := referenceInput source rewards C_star C_h rate
  let v := ReferenceInitializationRun.physical x b h
  let record := folded.records[j.val]
  have hfeedback := (hrecords record (List.getElem_mem j.isLt)).2.1
  have hslot : BootstrapCoordinatorLocalRound.coordinatorSlot p
      (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)) record.time =
      BootstrapPhysicalBlock.slot v record.time := by
    rfl
  have htuple : BootstrapCoordinatorLocalRound.coordinatorTupleArm p
      (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)) record.time =
      (BootstrapPhysicalBlock.tuple v record.time).val
        (ActiveRoundActions.coordinator p.two_le_m) := by
    rfl
  have hpositive := BootstrapPhysicalBlock.observationIndex_pos_iff v
    (BootstrapPhysicalBlock.run v record.time.val) record.time
    (ActiveRoundActions.coordinator p.two_le_m)
  have hcondition :
      (BootstrapPhysicalBlock.slot v record.time = PublicDiscreteDraws.downSlot ∧
        0 < (BootstrapPhysicalBlock.observationIndex v
          (BootstrapPhysicalBlock.run v record.time.val) record.time
          (ActiveRoundActions.coordinator p.two_le_m)).val) ↔
      (BootstrapPhysicalBlock.slot v record.time = PublicDiscreteDraws.downSlot ∧
        0 < BootstrapPhysicalBlock.feedback v
          (BootstrapPhysicalBlock.run v record.time.val) record.time
          (ActiveRoundActions.coordinator p.two_le_m)) := by
    rw [hpositive]
  have hdown : BootstrapCoordinatorLocalRound.downCreditArm p
      (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)) record.time
      (record.result.feedback (ActiveRoundActions.coordinator p.two_le_m)) =
      ReferenceInitializationRun.downArm x b h record.time := by
    unfold BootstrapCoordinatorLocalRound.downCreditArm ReferenceInitializationRun.downArm
    rw [hslot, htuple, hfeedback]
    rw [if_congr hcondition rfl rfl]
  change (if BootstrapCoordinatorLocalRound.downCreditArm p
      (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)) record.time
      (record.result.feedback (ActiveRoundActions.coordinator p.two_le_m)) = some arm then 1 else 0) = _
  rw [hdown]
  simp [BootstrapLaunchMonitor.creditCounter, x, record]

private theorem foldBlock_recordCredits_eq_referenceCalendarSum
    (source : SourceInput p) (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (rate : RateInput p) (C_star C_h : ℝ) (b : ReferenceInitializationRun.Boundary p)
    (h : b.completed < n_boot p)
    {foldStar foldH : ℝ}
    (folded : BlockFoldOutput p rate (ReferenceInitializationRun.nextBlock b h)
      source rewards foldStar foldH 0)
    (hrecords : ∀ record ∈ folded.records,
      record.result.actions = BootstrapPhysicalBlock.actions
        (ReferenceInitializationRun.physical
          (referenceInput source rewards C_star C_h rate) b h)
        (BootstrapPhysicalBlock.run
          (ReferenceInitializationRun.physical
            (referenceInput source rewards C_star C_h rate) b h) record.time.val)
        record.time ∧
      record.result.feedback = (fun i => BootstrapPhysicalBlock.observationIndex
        (ReferenceInitializationRun.physical
          (referenceInput source rewards C_star C_h rate) b h)
        (BootstrapPhysicalBlock.run
          (ReferenceInitializationRun.physical
            (referenceInput source rewards C_star C_h rate) b h) record.time.val)
        record.time i) ∧
      ∀ i, recordEntry record i = ReferenceInitializationRun.ownEntry
        (ReferenceInitializationRun.physical
          (referenceInput source rewards C_star C_h rate) b h) i record.time)
    (arm : Fin p.K) :
    recordsPositiveDownCredit folded.records arm =
      ∑ t ∈ calendarBlock p (ReferenceInitializationRun.nextBlock b h),
        BootstrapLaunchMonitor.creditCounter (fun _ => 0)
          (ReferenceInitializationRun.downArm
            (referenceInput source rewards C_star C_h rate) b h t) arm := by
  classical
  let target := calendarBlock p (ReferenceInitializationRun.nextBlock b h)
  have hsum : recordsPositiveDownCredit folded.records arm =
      ∑ j : Fin folded.records.length,
        recordPositiveDownCredit folded.records[j.val] arm := by
    unfold recordsPositiveDownCredit
    exact list_sum_map_eq_fin_sum folded.records
      (fun record => recordPositiveDownCredit record arm)
  rw [hsum]
  refine Finset.sum_bij (s := Finset.univ) (t := target)
    (fun j _ => folded.records[j.val].time) ?_ ?_ ?_ ?_
  · intro j _
    exact foldBlock_record_time_mem folded j
  · intro j _ k _ htimes
    apply Fin.ext
    have hj := foldBlock_record_time_value folded j
    have hk := foldBlock_record_time_value folded k
    have hval := congrArg Fin.val htimes
    omega
  · intro t ht
    obtain ⟨j, htime⟩ := foldBlock_record_time_surjective folded t ht
    exact ⟨j, Finset.mem_univ _, htime⟩
  · intro j _
    exact recordPositiveDownCredit_eq_referenceCredit source rewards rate C_star C_h b h
      folded hrecords j arm

private theorem foldBlockAux_prelaunch_terminal_monitor_le
    {rate : RateInput p} {block : Fin (n_boot p)}
    {source : SourceInput p} {rewards : ActualInitializationPhysicalStep.GridRewardTable p}
    {C_star C_h : ℝ} (cursor fuel : ℕ)
    (hbudget : cursor + fuel = BootstrapObservedFollower.blockLength p block)
    (phase : BootstrapCoordinatorLocalRound.Continuation p)
    (followers : Fin (p.m - 1) → ActualInitializationPhysicalStep.FollowerState p rate block)
    (hinvariant : ActualInitializationRun.BlockInvariant p rate block source C_star C_h
      cursor phase followers)
    (live : BootstrapCoordinatorLocalRound.PrelaunchBlock p)
    (hterminal : (ActualInitializationRun.foldBlockAux p rate block source rewards
      C_star C_h cursor fuel hbudget phase followers hinvariant).phase = .prelaunch live)
    (hpositive : 0 < fuel) :
    BootstrapLaunchMonitor.monitorValue p live.monitor.1.counters ≤
      4 * BootstrapStartupCostScale.Q C_star C_h p := by
  induction fuel generalizing cursor phase followers hinvariant live with
  | zero => omega
  | succ fuel ih =>
      have hcursor : cursor < BootstrapObservedFollower.blockLength p block := by omega
      cases phase with
      | launched launch =>
          have hdone := hinvariant.2.2.2
          omega
      | prelaunch coordinator =>
          let time := ActualInitializationRun.blockTime p block cursor hcursor
          let ready := ready_of_invariant rate block source C_star C_h
            cursor hcursor coordinator followers hinvariant
          let record := executeAt rate block time coordinator
            followers source rewards ready
          obtain ⟨hnext, hphase, hfollowers, hrecords⟩ := foldBlockAux_succ rate block
            source rewards C_star C_h cursor fuel (by omega) coordinator followers hinvariant
          let tail := ActualInitializationRun.foldBlockAux p rate block source rewards C_star C_h
            (cursor + 1) fuel (by omega) record.result.coordinator.next
            (fun i => (record.result.followers i).next) hnext
          have htailPhase : tail.phase = .prelaunch live := by
            change (ActualInitializationRun.foldBlockAux p rate block source rewards C_star C_h
              cursor (fuel + 1) (by omega) (.prelaunch coordinator) followers hinvariant).phase = _
              at hterminal
            rw [hphase] at hterminal
            exact hterminal
          cases fuel with
          | zero =>
              have hzero := foldBlockAux_zero rate block source rewards C_star C_h
                (cursor + 1) (by omega) record.result.coordinator.next
                (fun i => (record.result.followers i).next) hnext
              have hzeroPhase : tail.phase = record.result.coordinator.next := by
                simpa [tail] using hzero.1
              have hlast : record.result.coordinator.next = .prelaunch live :=
                hzeroPhase.symm.trans htailPhase
              have hnextEq := ActualInitializationRun.roundResult_next_eq record.result
              have hrecordInput := physicalRoundRecord_prepared_coordinatorInput record
              have hbefore : record.coordinatorBefore = coordinator := rfl
              have htimeEndpoint : BootstrapLaunchMonitor.calendarBlockEnd p time := by
                have htimeMem : time ∈ calendarBlock p block :=
                  ActualInitializationRun.blockTime_mem p block cursor hcursor
                have hstartLength : BootstrapObservedFollower.blockStart p block +
                    BootstrapObservedFollower.blockLength p block =
                    BootstrapObservedFollower.blockStop p block :=
                  ActualInitializationRun.blockStart_add_length_eq_stop p block
                have htimeVal : time.val = BootstrapObservedFollower.blockStart p block + cursor := by
                  rfl
                have hend : time.val + 1 = BootstrapObservedFollower.blockStop p block := by
                  rw [htimeVal, ← hstartLength]
                  simp only [Nat.add_assoc]
                  omega
                have hindex : BootstrapDimensions.roundBlockIndex p time = block := by
                  apply Fin.ext
                  exact (BootstrapDimensions.mem_calendarBlock_iff_quotient p block time).1
                    htimeMem |>.symm
                unfold BootstrapLaunchMonitor.calendarBlockEnd BootstrapDimensions.manuscriptRound
                rw [hindex]
                simpa [BootstrapObservedFollower.blockStop] using hend
              have hpreparedTime : record.result.prepared.time = time := by
                exact record.result_time.trans (by rfl)
              have htimeEndpoint' : BootstrapLaunchMonitor.calendarBlockEnd p
                  record.result.prepared.time := by
                rw [hpreparedTime]
                exact htimeEndpoint
              have htimeInput : record.result.prepared.time ∈
                  calendarBlock p record.result.prepared.coordinatorInput.data.block := by
                rw [record.result.prepared.readiness.1]
                exact record.result.prepared.readiness.2.1
              have hphaseObs := hnextEq.symm.trans hlast
              have htest : ¬ BootstrapCoordinatorLocalRound.launchTest p
                  record.result.prepared.coordinatorInput.data
                  record.result.prepared.coordinatorInput.monitor.1
                  record.result.prepared.time
                  (record.result.feedback (ActiveRoundActions.coordinator p.two_le_m)) := by
                intro htest
                simp [BootstrapCoordinatorLocalRound.continuationAfterObservation, htest]
                  at hphaseObs
              have hnot : ¬ BootstrapLaunchMonitor.monitorValue p
                  (BootstrapCoordinatorLocalRound.countersAfterObservation p
                    record.result.prepared.coordinatorInput.data.row
                    record.result.prepared.coordinatorInput.monitor.1.counters
                    record.result.prepared.time
                    (record.result.feedback (ActiveRoundActions.coordinator p.two_le_m))) >
                  4 * BootstrapStartupCostScale.Q
                    record.result.prepared.coordinatorInput.data.C_star
                    record.result.prepared.coordinatorInput.data.C_h p := by
                intro hgt
                apply htest
                exact ⟨htimeEndpoint', hgt⟩
              have hcounts := BootstrapCoordinatorLocalRound.continuationAfterObservation_monitor_counters
                p record.result.prepared.coordinatorInput.data
                record.result.prepared.coordinatorInput.monitor
                record.result.prepared.coordinatorInput.data.coordinator
                record.result.prepared.time htimeInput
                (record.result.feedback (ActiveRoundActions.coordinator p.two_le_m))
              rw [hphaseObs] at hcounts
              change live.monitor.1.counters =
                BootstrapCoordinatorLocalRound.countersAfterObservation p
                  record.result.prepared.coordinatorInput.data.row
                  record.result.prepared.coordinatorInput.monitor.1.counters
                  record.result.prepared.time
                  (record.result.feedback (ActiveRoundActions.coordinator p.two_le_m)) at hcounts
              have hdata : record.result.prepared.coordinatorInput = coordinator :=
                hrecordInput.trans hbefore
              have hstar : record.result.prepared.coordinatorInput.data.C_star = C_star := by
                exact congrArg (fun c : BootstrapCoordinatorLocalRound.PrelaunchBlock p =>
                  c.data.C_star) hdata ▸ hinvariant.1.2.2.2.2.1
              have hch : record.result.prepared.coordinatorInput.data.C_h = C_h := by
                exact congrArg (fun c : BootstrapCoordinatorLocalRound.PrelaunchBlock p =>
                  c.data.C_h) hdata ▸ hinvariant.1.2.2.2.2.2
              rw [hstar, hch] at hnot
              rw [hcounts]
              exact Nat.le_of_not_gt hnot
          | succ fuel' =>
              have htailBudget : cursor + 1 + (fuel' + 1) =
                  BootstrapObservedFollower.blockLength p block := by omega
              exact ih (cursor := cursor + 1) (phase := record.result.coordinator.next)
                (followers := fun i => (record.result.followers i).next)
                (hbudget := htailBudget) (hinvariant := hnext) (live := live)
                (hterminal := htailPhase) (hpositive := Nat.zero_lt_succ _)

/-- Terminal actual monitor counters are the reference boundary counters on
every arm. The sum is reindexed through the actual emitted record times and
their actual `calendarBlock` membership. -/
theorem foldBlock_updatedCounters_eq
    (source : SourceInput p) (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (rate : RateInput p) (C_star C_h : ℝ) (b : ReferenceInitializationRun.Boundary p)
    (h : b.completed < n_boot p)
    (actual : ActualInitializationRun.BlockCarry p rate (ReferenceInitializationRun.nextBlock b h))
    (past : List (ActualInitializationRun.PhysicalRoundRecord p rate source rewards))
    (hr : BlockStartRelated source rewards C_star C_h rate
      (ReferenceInitializationRun.nextBlock b h) actual b past)
    (hdown : ∀ i, ¬ InitializationFailureProvenance.generatedBlockDown
      (referenceInput source rewards C_star C_h rate) b h i) :
    (ActualInitializationRun.foldBlock p rate (ReferenceInitializationRun.nextBlock b h)
      source rewards actual).phase.monitorState.counters =
      ReferenceInitializationRun.updatedCounters
        (referenceInput source rewards C_star C_h rate) b h := by
  let x := referenceInput source rewards C_star C_h rate
  let folded := ActualInitializationRun.foldBlock p rate (ReferenceInitializationRun.nextBlock b h)
    source rewards actual
  obtain ⟨_, _, hrecords, _⟩ := foldBlock_related source rewards rate C_star C_h b h
    actual past hr hdown
  funext arm
  have hactual := ActualInitializationMonitorTrace.foldBlock_counter_identity
    (source := source) (rewards := rewards) (carry := actual) arm
  have hrecordSum := foldBlock_recordCredits_eq_referenceCalendarSum source rewards rate
    C_star C_h b h folded hrecords arm
  rw [hactual, hr.2.2.2.1, ReferenceInitializationRun.updatedCounters_eq_credit_fold,
    hrecordSum]

/-- The exact strict launch test has the same monitor value and the same
`C_star` and `C_h` on the actual and reference sides. -/
theorem foldBlock_strictCrossing_eq
    (source : SourceInput p) (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (rate : RateInput p) (C_star C_h : ℝ) (b : ReferenceInitializationRun.Boundary p)
    (h : b.completed < n_boot p)
    (actual : ActualInitializationRun.BlockCarry p rate (ReferenceInitializationRun.nextBlock b h))
    (past : List (ActualInitializationRun.PhysicalRoundRecord p rate source rewards))
    (hr : BlockStartRelated source rewards C_star C_h rate
      (ReferenceInitializationRun.nextBlock b h) actual b past)
    (hdown : ∀ i, ¬ InitializationFailureProvenance.generatedBlockDown
      (referenceInput source rewards C_star C_h rate) b h i) :
    let x := referenceInput source rewards C_star C_h rate
    let folded := ActualInitializationRun.foldBlock p rate (ReferenceInitializationRun.nextBlock b h)
      source rewards actual
    BootstrapLaunchMonitor.monitorValue p folded.phase.monitorState.counters >
        4 * BootstrapStartupCostScale.Q actual.C_star actual.C_h p ↔
      ReferenceInitializationRun.crosses x b h = true := by
  let x := referenceInput source rewards C_star C_h rate
  let folded := ActualInitializationRun.foldBlock p rate (ReferenceInitializationRun.nextBlock b h)
    source rewards actual
  have hcounters := foldBlock_updatedCounters_eq source rewards rate C_star C_h b h actual past hr hdown
  have hstar := hr.2.2.2.2.1
  have hch := hr.2.2.2.2.2.1
  change BootstrapLaunchMonitor.monitorValue p folded.phase.monitorState.counters >
      4 * BootstrapStartupCostScale.Q actual.C_star actual.C_h p ↔
    ReferenceInitializationRun.crosses x b h = true
  rw [hcounters, hstar, hch]
  simp [ReferenceInitializationRun.crosses, x, referenceInput]

private theorem foldBlock_prelaunch_terminal_monitor_le
    (source : SourceInput p) (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (rate : RateInput p) (block : Fin (n_boot p))
    (carry : ActualInitializationRun.BlockCarry p rate block)
    (live : BootstrapCoordinatorLocalRound.PrelaunchBlock p)
    (hphase : (ActualInitializationRun.foldBlock p rate block source rewards carry).phase =
      .prelaunch live) :
    BootstrapLaunchMonitor.monitorValue p live.monitor.1.counters ≤
      4 * BootstrapStartupCostScale.Q carry.C_star carry.C_h p := by
  have hlength : 0 < BootstrapObservedFollower.blockLength p block := by
    have hstart := BootstrapObservedFollower.blockStart_lt_blockStop p block
    unfold BootstrapObservedFollower.blockLength
    omega
  let started := ActualInitializationRun.beginBlock p rate block source carry
  have haux : (ActualInitializationRun.foldBlockAux p rate block source rewards
      carry.C_star carry.C_h 0 (BootstrapObservedFollower.blockLength p block) (by simp)
      (.prelaunch started.coordinator) started.followers started.invariant).phase =
      .prelaunch live := by
    simpa [ActualInitializationRun.foldBlock, started] using hphase
  have hbound := foldBlockAux_prelaunch_terminal_monitor_le (rate := rate) (block := block)
    (source := source) (rewards := rewards) (C_star := carry.C_star) (C_h := carry.C_h)
    0 (BootstrapObservedFollower.blockLength p block) (by simp)
    (.prelaunch started.coordinator) started.followers started.invariant live haux hlength
  exact hbound

/-- A computed actual continuation carries the no-crossing boundary value
forced by the literal final physical launch test. Combined with the exact
record-based counter comparison, this gives the reference's strict Boolean
test without adding it as a handoff premise. -/
theorem continueNext_reference_no_crossing
    (source : SourceInput p) (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (rate : RateInput p) (C_star C_h : ℝ) (b : ReferenceInitializationRun.Boundary p)
    (h : b.completed < n_boot p)
    (actual : ActualInitializationRun.BlockCarry p rate (ReferenceInitializationRun.nextBlock b h))
    (past : List (ActualInitializationRun.PhysicalRoundRecord p rate source rewards))
    (hr : BlockStartRelated source rewards C_star C_h rate
      (ReferenceInitializationRun.nextBlock b h) actual b past)
    (hdown : ∀ i, ¬ InitializationFailureProvenance.generatedBlockDown
      (referenceInput source rewards C_star C_h rate) b h i)
    (next : Fin (n_boot p))
    (nextCarry : ActualInitializationRun.BlockCarry p rate next)
    (hcontinue : (ActualInitializationRun.combinedBoundaryHandoff p rate
      (ReferenceInitializationRun.nextBlock b h) source rewards actual.C_star actual.C_h
      (ActualInitializationRun.foldBlock p rate (ReferenceInitializationRun.nextBlock b h)
        source rewards actual)).disposition = .continueNext next nextCarry) :
    ReferenceInitializationRun.crosses (referenceInput source rewards C_star C_h rate) b h = false := by
  let block := ReferenceInitializationRun.nextBlock b h
  let folded := ActualInitializationRun.foldBlock p rate block source rewards actual
  have hfacts := ActualInitializationHorizon.combinedBoundaryHandoff_continueNext_facts
    folded next nextCarry (by simpa [block, folded] using hcontinue)
  obtain ⟨_, _, _, live, hphase, _, _, _⟩ := hfacts
  have hbound := foldBlock_prelaunch_terminal_monitor_le source rewards rate
    block actual live (by simpa [folded] using hphase)
  have hstrict := foldBlock_strictCrossing_eq source rewards rate C_star C_h b h actual past hr hdown
  have hboundActual : BootstrapLaunchMonitor.monitorValue p folded.phase.monitorState.counters ≤
      4 * BootstrapStartupCostScale.Q actual.C_star actual.C_h p := by
    rw [hphase]
    exact hbound
  have hnot : ¬ BootstrapLaunchMonitor.monitorValue p folded.phase.monitorState.counters >
      4 * BootstrapStartupCostScale.Q actual.C_star actual.C_h p :=
    Nat.not_lt_of_ge hboundActual
  cases hc : ReferenceInitializationRun.crosses
      (referenceInput source rewards C_star C_h rate) b h with
  | false => rfl
  | true =>
      have hgt := hstrict.mpr hc
      exact False.elim (hnot hgt)

/-- The exhausted disposition is the clipped final prelaunch boundary. It
does not assert a launch: its actual monitor stays at the no-launch sentinel,
the reference strict test is false, and the emitted physical records stop at
the genuine horizon endpoint. -/
private theorem exhausted_handoff_phase
    (source : SourceInput p) (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (rate : RateInput p) (block : Fin (n_boot p))
    (C_star C_h : ℝ)
    (folded : ActualInitializationRun.BlockFoldOutput p rate block source rewards C_star C_h 0)
    (live : BootstrapCoordinatorLocalRound.PrelaunchBlock p)
    (hexhausted : (ActualInitializationRun.combinedBoundaryHandoff p rate block source rewards
      C_star C_h folded).disposition = .exhausted live) :
    folded.phase = .prelaunch live := by
  cases folded with
  | mk consumed phase followers records invariant consumed_eq_blockLength record_count chronological =>
      cases phase with
      | launched launch =>
          dsimp [ActualInitializationRun.combinedBoundaryHandoff, id] at hexhausted
          cases hexhausted
      | prelaunch current =>
          by_cases hlast : block.val + 1 = n_boot p
          · dsimp [ActualInitializationRun.combinedBoundaryHandoff, id] at hexhausted
            rw [dite_eq_left hlast] at hexhausted
            have hcurrent : current = live := by
              simpa only [BoundaryDisposition.exhausted.injEq] using hexhausted
            subst current
            rfl
          · dsimp [ActualInitializationRun.combinedBoundaryHandoff, id] at hexhausted
            rw [dite_eq_right hlast] at hexhausted
            cases hexhausted

theorem exhausted_reference_no_crossing
    (source : SourceInput p) (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (rate : RateInput p) (C_star C_h : ℝ) (b : ReferenceInitializationRun.Boundary p)
    (h : b.completed < n_boot p)
    (actual : ActualInitializationRun.BlockCarry p rate (ReferenceInitializationRun.nextBlock b h))
    (past : List (ActualInitializationRun.PhysicalRoundRecord p rate source rewards))
    (hr : BlockStartRelated source rewards C_star C_h rate
      (ReferenceInitializationRun.nextBlock b h) actual b past)
    (hdown : ∀ i, ¬ InitializationFailureProvenance.generatedBlockDown
      (referenceInput source rewards C_star C_h rate) b h i)
    (live : BootstrapCoordinatorLocalRound.PrelaunchBlock p)
    (hexhausted : (ActualInitializationRun.combinedBoundaryHandoff p rate
      (ReferenceInitializationRun.nextBlock b h) source rewards actual.C_star actual.C_h
      (ActualInitializationRun.foldBlock p rate (ReferenceInitializationRun.nextBlock b h)
        source rewards actual)).disposition = .exhausted live) :
    let x := referenceInput source rewards C_star C_h rate
    let block := ReferenceInitializationRun.nextBlock b h
    let folded := ActualInitializationRun.foldBlock p rate block source rewards actual
    block.val + 1 = n_boot p ∧ folded.phase = .prelaunch live ∧
      ReferenceInitializationRun.crosses x b h = false ∧
      (∀ i, (ReferenceInitializationRun.finishBlock x b h).forcedFailure i =
        b.forcedFailure i) ∧
      BootstrapObservedFollower.blockStop p block = p.T ∧
      (∀ r ∈ folded.records, r.time.val < p.T) ∧
      (∀ i, match folded.followers i with
        | .bootstrap _ =>
            (BootstrapObservedFollower.nextActivationRound p block).val = p.T + 1
        | .declared _ _ _ => True) := by
  let x := referenceInput source rewards C_star C_h rate
  let block := ReferenceInitializationRun.nextBlock b h
  let folded := ActualInitializationRun.foldBlock p rate block source rewards actual
  have hdisposition : (ActualInitializationRun.combinedBoundaryHandoff p rate block source rewards
      actual.C_star actual.C_h folded).disposition = .exhausted live := by
    simpa [block, folded] using hexhausted
  have hlast : block.val + 1 = n_boot p :=
    ActualInitializationHorizon.combinedBoundaryHandoff_exhausted_last
      folded live hdisposition
  have hphase := exhausted_handoff_phase source rewards rate block actual.C_star actual.C_h
    folded live hdisposition
  have hbound := foldBlock_prelaunch_terminal_monitor_le source rewards rate
    block actual live (by simpa [folded] using hphase)
  have hstrict := foldBlock_strictCrossing_eq source rewards rate C_star C_h b h
    actual past hr hdown
  have hboundActual : BootstrapLaunchMonitor.monitorValue p folded.phase.monitorState.counters ≤
      4 * BootstrapStartupCostScale.Q actual.C_star actual.C_h p := by
    rw [hphase]
    exact hbound
  have hnot : ¬ BootstrapLaunchMonitor.monitorValue p folded.phase.monitorState.counters >
      4 * BootstrapStartupCostScale.Q actual.C_star actual.C_h p :=
    Nat.not_lt_of_ge hboundActual
  have hcross : ReferenceInitializationRun.crosses x b h = false := by
    cases hc : ReferenceInitializationRun.crosses x b h with
    | false => rfl
    | true =>
        have hgt := hstrict.mpr hc
        exact False.elim (hnot hgt)
  have hforced (i : ActiveRoundActions.Follower p.m) :
      ReferenceInitializationRun.forced x b h i = false := by
    simp [ReferenceInitializationRun.forced, hcross]
  refine ⟨hlast, hphase, hcross, ?_, ?_, ?_, ?_⟩
  · intro i
    change (b.forcedFailure i || ReferenceInitializationRun.forced x b h i) =
      b.forcedFailure i
    rw [hforced i]
    cases b.forcedFailure i <;> rfl
  · exact BootstrapObservedFollower.finalBlock_endpoint_eq_T p block hlast
  · intro r _
    exact r.time.isLt
  · intro i
    cases hf : folded.followers i with
    | bootstrap state =>
        simpa [hf] using
          BootstrapObservedFollower.nextActivationRound_final_eq_T_succ p block hlast
    | declared row activation configuration => simp [hf]

private theorem continueNext_follower_start_related
    (source : SourceInput p) (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (rate : RateInput p) (C_star C_h : ℝ) (b : ReferenceInitializationRun.Boundary p)
    (h : b.completed < n_boot p)
    (actual : ActualInitializationRun.BlockCarry p rate (ReferenceInitializationRun.nextBlock b h))
    (past : List (ActualInitializationRun.PhysicalRoundRecord p rate source rewards))
    (hr : BlockStartRelated source rewards C_star C_h rate
      (ReferenceInitializationRun.nextBlock b h) actual b past)
    (hdown : ∀ i, ¬ InitializationFailureProvenance.generatedBlockDown
      (referenceInput source rewards C_star C_h rate) b h i)
    (hcross : ReferenceInitializationRun.crosses
      (referenceInput source rewards C_star C_h rate) b h = false)
    (next : Fin (n_boot p)) (nextCarry : ActualInitializationRun.BlockCarry p rate next)
    (hcarryMap : ∀ j, nextCarry.followers j =
      ActualInitializationRun.followerCarryAtBlockBoundary p rate
        (ReferenceInitializationRun.nextBlock b h)
        ((ActualInitializationRun.foldBlock p rate (ReferenceInitializationRun.nextBlock b h)
          source rewards actual).followers j))
    (hclean : ∀ (i : Fin (p.m - 1))
      (hi : refFollower i ∈ (ReferenceInitializationRun.physical
        (referenceInput source rewards C_star C_h rate) b h).uninformed),
      BootstrapAllCandidateController.cleanPrefix
        (ReferenceInitializationRun.physical (referenceInput source rewards C_star C_h rate) b h)
        source.1.2 ⟨refFollower i, hi⟩
        (ActualInitializationPhysicalStep.selectedRowIndex p source) p.T)
    (i : Fin (p.m - 1)) :
    follower_start_related (referenceInput source rewards C_star C_h rate)
      source rate rfl (ReferenceInitializationRun.finishBlock
        (referenceInput source rewards C_star C_h rate) b h) i (nextCarry.followers i) := by
  classical
  let x := referenceInput source rewards C_star C_h rate
  let block := ReferenceInitializationRun.nextBlock b h
  let folded := ActualInitializationRun.foldBlock p rate block source rewards actual
  let hrOriginal := hr
  rcases hr with ⟨hcompleted, hcrossing, hforced, hcounter, hstar, hch, hpast, hfollower⟩
  have hcross' : ReferenceInitializationRun.crosses x b h = false := by
    change ReferenceInitializationRun.crosses
      (referenceInput source rewards C_star C_h rate) b h = false
    exact hcross
  have hforceNow : ReferenceInitializationRun.forced x b h (refFollower i) = false := by
    unfold ReferenceInitializationRun.forced
    rw [hcross']
    rfl
  have hfinishForced :
      (ReferenceInitializationRun.finishBlock x b h).forcedFailure (refFollower i) = false := by
    change (b.forcedFailure (refFollower i) || ReferenceInitializationRun.forced x b h
      (refFollower i)) = false
    rw [hforced (refFollower i), hforceNow]
    rfl
  obtain ⟨hm, hcursor, _, _⟩ := foldBlock_related source rewards rate C_star C_h b h
    actual past hrOriginal hdown
  have hround := (hcursor.2.2.2.2 i).1
  cases hactual : actual.followers i with
  | bootstrap numerators lower =>
      have hstart : b.activation (refFollower i) = none ∧ numerators = b.numerators i := by
        simpa [ActualReferenceInitializationBlock.follower_start_related, hactual] using
          hfollower i
      have hhi : refFollower i ∈
          (ReferenceInitializationRun.physical x b h).uninformed :=
        (ReferenceInitializationRun.mem_uninformed b (refFollower i)).2 hstart.1
      have hhiBare : refFollower i ∈ ReferenceInitializationRun.uninformed b := by
        change refFollower i ∈ (ReferenceInitializationRun.physical x b h).uninformed
        exact hhi
      obtain ⟨state, hout, _, _, _, hupdated, hpending, _, _⟩ :=
        foldBlock_bootstrap_comparison source rewards rate C_star C_h b h actual past hrOriginal hdown
          i hhi (hclean i hhi)
      have hpendingBare : BootstrapObservedFollower.pendingDeclaration state.blockCase =
          if (ReferenceInitializationRun.candidate x b h
            ⟨refFollower i, hhiBare⟩).pending = true then
            some (ActualInitializationPhysicalStep.selectedRowIndex p source) else none := by
        exact hpending
      cases hpend : BootstrapObservedFollower.pendingDeclaration state.blockCase with
      | none =>
          have hcand : (ReferenceInitializationRun.candidate x b h
              ⟨refFollower i, hhiBare⟩).pending = false := by
            cases hcand : (ReferenceInitializationRun.candidate x b h
              ⟨refFollower i, hhiBare⟩).pending with
            | false => rfl
            | true =>
                have heq := hpendingBare
                rw [hpend, hcand] at heq
                simp at heq
          have hactivation : (ReferenceInitializationRun.finishBlock x b h).activation
              (refFollower i) = none := by
            change ReferenceInitializationRun.finalActivation x b h (refFollower i) = none
            rw [ReferenceInitializationRun.finalActivation, hforceNow]
            simp [ReferenceInitializationRun.declaredActivation, hhiBare, hcand]
          have hmap := hcarryMap i
          rw [hout] at hmap
          simp only [ActualInitializationRun.followerCarryAtBlockBoundary,
            ActualInitializationRun.followerCarryOfBoundaryOutput,
            ActualInitializationRun.boundaryOutputFromFollower, hpend] at hmap
          rw [hmap]
          change (ReferenceInitializationRun.finishBlock x b h).activation (refFollower i) = none ∧
            BootstrapObservedFollower.updatedNumerators p block state =
              (ReferenceInitializationRun.finishBlock x b h).numerators i
          refine ⟨hactivation, ?_⟩
          simpa [ReferenceInitializationRun.finishBlock] using hupdated
      | some row =>
          have hcand : (ReferenceInitializationRun.candidate x b h
              ⟨refFollower i, hhiBare⟩).pending = true := by
            cases hcand : (ReferenceInitializationRun.candidate x b h
              ⟨refFollower i, hhiBare⟩).pending with
            | false =>
                have heq := hpendingBare
                rw [hpend, hcand] at heq
                simp at heq
            | true => rfl
          have hrow : row = ActualInitializationPhysicalStep.selectedRowIndex p source := by
            have heq := hpendingBare
            rw [hpend, hcand] at heq
            exact Option.some.inj heq
          have hstop : ReferenceInitializationRun.elapsed p (b.completed + 1) =
              BootstrapObservedFollower.blockStop p block := by
            simp [ReferenceInitializationRun.elapsed, block,
              ReferenceInitializationRun.nextBlock, BootstrapObservedFollower.blockStop]
          have hactivation : BootstrapObservedFollower.nextActivationRound p block =
              ReferenceInitializationRun.boundaryActivation b := by
            apply Subtype.ext
            simpa [BootstrapObservedFollower.nextActivationRound,
              ReferenceInitializationRun.boundaryActivation] using hstop.symm
          have hfinishActivation : (ReferenceInitializationRun.finishBlock x b h).activation
              (refFollower i) = some (BootstrapObservedFollower.nextActivationRound p block) := by
            rw [ReferenceInitializationRun.saved_activation x b h ⟨refFollower i, hhi⟩ hcand,
              hactivation]
          have hfinishOrd := ReferenceInitializationRun.ordinary_finishBlock_of_saved x b h
            ⟨refFollower i, hhi⟩ hcand (hforced (refFollower i))
          have hmap := hcarryMap i
          rw [hout] at hmap
          simp only [ActualInitializationRun.followerCarryAtBlockBoundary,
            ActualInitializationRun.followerCarryOfBoundaryOutput,
            ActualInitializationRun.boundaryOutputFromFollower, hpend, Option.elim_some]
            at hmap
          have hmap' : nextCarry.followers i =
              .declared (ActualInitializationPhysicalStep.selectedRowIndex p source)
                (BootstrapObservedFollower.nextActivationRound p block)
                (.ordinary (ReferenceInitializationRun.ordinary x
                  (ReferenceInitializationRun.finishBlock x b h) (refFollower i))
                  (ActiveFollowerLifecycle.initialMemory p)) := by
            rw [hrow] at hmap
            rw [hfinishOrd]
            exact hmap
          have hfresh : ReferencePrelaunchFollower.replay rate.eta i x.row
              (BootstrapObservedFollower.nextActivationRound p block)
              ((ReferenceInitializationRun.finishBlock x b h).history
                (PublicDiscreteDraws.followerPlayer p.two_le_m (refFollower i)))
              (ReferenceInitializationRun.elapsed_le_T p (b.completed + 1)) =
              ReferencePrelaunchFollower.initial p rate.eta := by
            exact ReferencePrelaunchFollower.replay_before_activation rate.eta i x.row
              (BootstrapObservedFollower.nextActivationRound p block)
              ((ReferenceInitializationRun.finishBlock x b h).history
                (PublicDiscreteDraws.followerPlayer p.two_le_m (refFollower i)))
              (ReferenceInitializationRun.elapsed_le_T p (b.completed + 1)) (by
                rw [hactivation]
                simp [ReferenceInitializationRun.boundaryActivation,
                  ReferenceInitializationRun.finishBlock])
          have hfreshBuffer : (ReferencePrelaunchFollower.replay rate.eta i x.row
              (BootstrapObservedFollower.nextActivationRound p block)
              ((ReferenceInitializationRun.finishBlock x b h).history
                (PublicDiscreteDraws.followerPlayer p.two_le_m (refFollower i)))
              (ReferenceInitializationRun.elapsed_le_T p (b.completed + 1))).buffer = [] := by
            simpa [ReferencePrelaunchFollower.initial] using
              congrArg (fun state => state.buffer) hfresh
          have hfreshDownBatch : (ReferencePrelaunchFollower.replay rate.eta i x.row
              (BootstrapObservedFollower.nextActivationRound p block)
              ((ReferenceInitializationRun.finishBlock x b h).history
                (PublicDiscreteDraws.followerPlayer p.two_le_m (refFollower i)))
              (ReferenceInitializationRun.elapsed_le_T p (b.completed + 1))).downBatch =
              AffineBatchDecoder.initial p := by
            simpa [ReferencePrelaunchFollower.initial] using
              congrArg (fun state => state.downBatch) hfresh
          rw [hmap']
          unfold ActualReferenceInitializationBlock.follower_start_related
          refine ⟨rfl, hfinishActivation, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · exact (ReferenceInitializationRun.ordinary_registers x
              (ReferenceInitializationRun.finishBlock x b h) (refFollower i)).1
          · exact (ReferenceInitializationRun.ordinary_registers x
              (ReferenceInitializationRun.finishBlock x b h) (refFollower i)).2.1
          · exact (ReferenceInitializationRun.ordinary_registers x
              (ReferenceInitializationRun.finishBlock x b h) (refFollower i)).2.2.1
          · exact (ReferenceInitializationRun.ordinary_registers x
              (ReferenceInitializationRun.finishBlock x b h) (refFollower i)).2.2.2.1
          · exact (ReferenceInitializationRun.ordinary_registers x
              (ReferenceInitializationRun.finishBlock x b h) (refFollower i)).2.2.2.2.1
          · exact (ReferenceInitializationRun.ordinary_registers x
              (ReferenceInitializationRun.finishBlock x b h) (refFollower i)).2.2.2.2.2
          · simp [hfinishOrd, ReferencePrelaunchFollower.initial]
          · simpa [hfinishOrd, ReferencePrelaunchFollower.initial] using hfreshBuffer.symm
          · simpa [hfinishOrd, ReferencePrelaunchFollower.initial] using hfreshDownBatch.symm
  | declared row activation configuration =>
      cases configuration with
      | dagger =>
          have hfalse := hfollower i
          simp [hactual, ActualReferenceInitializationBlock.follower_start_related] at hfalse
      | ordinary state memory =>
          have hstart : row = ActualInitializationPhysicalStep.selectedRowIndex p source ∧
              b.activation (refFollower i) = some activation ∧
              state = ReferenceInitializationRun.ordinary x b (refFollower i) ∧
              state.lastDown = none ∧ ReferencePrelaunchFollower.acceptedStart state = 0 ∧
              state.S = 0 ∧ state.delta = 0 ∧ state.backlog = 0 ∧
              state.status = .unoccupied ∧ state.initializationFailure = false ∧
              state.buffer = (ReferencePrelaunchFollower.replay rate.eta i x.row activation
                (b.history (PublicDiscreteDraws.followerPlayer p.two_le_m (refFollower i)))
                (ReferenceInitializationRun.elapsed_le_T p b.completed)).buffer ∧
              state.downBatch = (ReferencePrelaunchFollower.replay rate.eta i x.row activation
                (b.history (PublicDiscreteDraws.followerPlayer p.two_le_m (refFollower i)))
                (ReferenceInitializationRun.elapsed_le_T p b.completed)).downBatch := by
            simpa [ActualReferenceInitializationBlock.follower_start_related, hactual] using
              hfollower i
          have hout := foldBlock_declared_comparison source rewards rate C_star C_h b h
            actual past hrOriginal hdown i row activation state memory hactual
          have hmap := hcarryMap i
          rw [hout] at hmap
          simp only [ActualInitializationRun.followerCarryAtBlockBoundary,
            ActualInitializationRun.followerCarryOfBoundaryOutput,
            ActualInitializationRun.boundaryOutputFromFollower] at hmap
          have hfinishActivation : (ReferenceInitializationRun.finishBlock x b h).activation
              (refFollower i) = some activation :=
            ReferenceInitializationRun.activated_activation x b h (refFollower i) activation hstart.2.1
          have hmap' : nextCarry.followers i =
              .declared (ActualInitializationPhysicalStep.selectedRowIndex p source) activation
                (.ordinary (ReferenceInitializationRun.ordinary x
                  (ReferenceInitializationRun.finishBlock x b h) (refFollower i)) memory) := by
            exact hmap
          have hrelOut := (hcursor.2.2.2.2 i).1
          rw [hout] at hrelOut
          simp only [ActualReferenceInitializationBlock.round_follower_related] at hrelOut
          obtain ⟨_, _, hstateReplay, hfailure⟩ := hrelOut
          have hordinaryFields :
              (ReferenceInitializationRun.ordinary x (ReferenceInitializationRun.finishBlock x b h)
                (refFollower i)).buffer =
                (ReferencePrelaunchFollower.replay rate.eta i x.row activation
                  ((ReferenceInitializationRun.finishBlock x b h).history
                    (PublicDiscreteDraws.followerPlayer p.two_le_m (refFollower i)))
                  (ReferenceInitializationRun.elapsed_le_T p (b.completed + 1))).buffer ∧
              (ReferenceInitializationRun.ordinary x (ReferenceInitializationRun.finishBlock x b h)
                (refFollower i)).downBatch =
                (ReferencePrelaunchFollower.replay rate.eta i x.row activation
                  ((ReferenceInitializationRun.finishBlock x b h).history
                    (PublicDiscreteDraws.followerPlayer p.two_le_m (refFollower i)))
                  (ReferenceInitializationRun.elapsed_le_T p (b.completed + 1))).downBatch := by
            unfold ReferenceInitializationRun.ordinary
            rw [hfinishForced, hfinishActivation]
            exact ReferencePrelaunchFollower.atLaunch_preserves _
          rw [hmap']
          unfold ActualReferenceInitializationBlock.follower_start_related
          refine ⟨rfl, hfinishActivation, rfl, ?_, ?_, ?_, ?_, ?_, ?_, hfailure, ?_, ?_⟩
          · exact (ReferenceInitializationRun.ordinary_registers x
              (ReferenceInitializationRun.finishBlock x b h) (refFollower i)).1
          · exact (ReferenceInitializationRun.ordinary_registers x
              (ReferenceInitializationRun.finishBlock x b h) (refFollower i)).2.1
          · exact (ReferenceInitializationRun.ordinary_registers x
              (ReferenceInitializationRun.finishBlock x b h) (refFollower i)).2.2.1
          · exact (ReferenceInitializationRun.ordinary_registers x
              (ReferenceInitializationRun.finishBlock x b h) (refFollower i)).2.2.2.1
          · exact (ReferenceInitializationRun.ordinary_registers x
              (ReferenceInitializationRun.finishBlock x b h) (refFollower i)).2.2.2.2.1
          · exact (ReferenceInitializationRun.ordinary_registers x
              (ReferenceInitializationRun.finishBlock x b h) (refFollower i)).2.2.2.2.2
          · exact hordinaryFields.1
          · exact hordinaryFields.2

/-- The computed actual continuation is the next reference block start. Its
counter, shared constants, prior physical records, and each carried follower
state agree with the completed reference boundary. The literal clean-prefix
condition is exposed only for followers still in bootstrap; all other local
state, history, memory, and partial decoder data are retained by the accepted
boundary operations. -/
theorem combinedBoundaryHandoff_continueNext_related
    (source : SourceInput p) (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (rate : RateInput p) (C_star C_h : ℝ) (b : ReferenceInitializationRun.Boundary p)
    (h : b.completed < n_boot p)
    (actual : ActualInitializationRun.BlockCarry p rate (ReferenceInitializationRun.nextBlock b h))
    (past : List (ActualInitializationRun.PhysicalRoundRecord p rate source rewards))
    (hr : BlockStartRelated source rewards C_star C_h rate
      (ReferenceInitializationRun.nextBlock b h) actual b past)
    (hdown : ∀ i, ¬ InitializationFailureProvenance.generatedBlockDown
      (referenceInput source rewards C_star C_h rate) b h i)
    (hclean : ∀ (i : Fin (p.m - 1))
      (hi : refFollower i ∈ (ReferenceInitializationRun.physical
        (referenceInput source rewards C_star C_h rate) b h).uninformed),
      BootstrapAllCandidateController.cleanPrefix
        (ReferenceInitializationRun.physical (referenceInput source rewards C_star C_h rate) b h)
        source.1.2 ⟨refFollower i, hi⟩
        (ActualInitializationPhysicalStep.selectedRowIndex p source) p.T)
    (next : Fin (n_boot p)) (nextCarry : ActualInitializationRun.BlockCarry p rate next)
    (hcontinue : (ActualInitializationRun.combinedBoundaryHandoff p rate
      (ReferenceInitializationRun.nextBlock b h) source rewards actual.C_star actual.C_h
      (ActualInitializationRun.foldBlock p rate (ReferenceInitializationRun.nextBlock b h)
        source rewards actual)).disposition = .continueNext next nextCarry) :
    next.val = b.completed + 1 ∧
      BlockStartRelated source rewards C_star C_h rate next nextCarry
        (ReferenceInitializationRun.finishBlock
          (referenceInput source rewards C_star C_h rate) b h)
        (past ++ (ActualInitializationRun.foldBlock p rate
          (ReferenceInitializationRun.nextBlock b h) source rewards actual).records) := by
  let x := referenceInput source rewards C_star C_h rate
  let block := ReferenceInitializationRun.nextBlock b h
  let folded := ActualInitializationRun.foldBlock p rate block source rewards actual
  have hcontinue' : (ActualInitializationRun.combinedBoundaryHandoff p rate block source rewards
      actual.C_star actual.C_h folded).disposition = .continueNext next nextCarry := by
    simpa [block, folded] using hcontinue
  have hfacts := ActualInitializationHorizon.combinedBoundaryHandoff_continueNext_facts
    folded next nextCarry hcontinue'
  obtain ⟨hnextval, hCstar, hCh, live, hphase, hcoordinator, hmonitor, hfollowers⟩ := hfacts
  let hrOriginal := hr
  rcases hr with ⟨hcompleted, hcrossing, hforced, hcounter, hstar, hch, _, _⟩
  have hnextval' : next.val = b.completed + 1 := by omega
  have hcross : ReferenceInitializationRun.crosses x b h = false :=
    continueNext_reference_no_crossing source rewards rate C_star C_h b h actual past
      hrOriginal
      hdown next nextCarry hcontinue
  have hboundaryForced (i : ActiveRoundActions.Follower p.m) :
      (ReferenceInitializationRun.finishBlock x b h).forcedFailure i = false := by
    change (b.forcedFailure i || ReferenceInitializationRun.forced x b h i) = false
    have hforcedNow : ReferenceInitializationRun.forced x b h i = false := by
      unfold ReferenceInitializationRun.forced
      rw [hcross]
      rfl
    rw [hforced i, hforcedNow]
    rfl
  have hmonitorState := ActualInitializationMonitorTrace.combinedBoundaryHandoff_continueNext_monitor
    folded next nextCarry hcontinue'
  have hcounterOut : nextCarry.monitor.1.counters =
      (ReferenceInitializationRun.finishBlock x b h).counters := by
    rw [hmonitorState]
    simpa [ReferenceInitializationRun.finishBlock] using
      foldBlock_updatedCounters_eq source rewards rate C_star C_h b h actual past
        hrOriginal hdown
  have hpastOut := foldBlock_past_related source rewards rate C_star C_h b h
    actual past hrOriginal hdown
  have hfollowersOut (i : Fin (p.m - 1)) :
      follower_start_related x source rate rfl (ReferenceInitializationRun.finishBlock x b h)
        i (nextCarry.followers i) := by
    exact continueNext_follower_start_related source rewards rate C_star C_h b h actual past
      hrOriginal
      hdown hcross next nextCarry hfollowers hclean i
  refine ⟨hnextval', ?_⟩
  refine ⟨?_, ?_, hboundaryForced, hcounterOut, ?_, ?_, hpastOut, hfollowersOut⟩
  · change b.completed + 1 = next.val
    omega
  · simp [ReferenceInitializationRun.finishBlock, x, hcross]
  · exact hCstar.trans hstar
  · exact hCh.trans hch

end Bandits.Support.ActualReferenceInitializationBoundary

end
