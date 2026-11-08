/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ActualInitializationHorizon

import Lean.Elab.Tactic.Omega

/-!
# Actual initialization monitor trace

Counter lineage for the computed actual initialization run. The monitor
credits the selected coordinator row's physical DOWN-positive observation on
the record's calendar round, including the final observation before a block
boundary test. Sources: `sources/zip4/manuscript/07_public_setup.tex:39-57,100-140`
for the coordinator counters and their block-boundary use. This is internal
deterministic accounting, without a threshold or source-facing closure claim.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.BootstrapCoordinatorLocalRound
open Bandits.Support.BootstrapLaunchMonitor
open Bandits.Support.ActualInitializationPhysicalStep
open Bandits.Support.ActualInitializationRun
open Bandits.Support.ActualInitializationHorizon
open Bandits.Support.ActiveRoundActions

namespace Bandits.Support.ActualInitializationMonitorTrace

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := Bandits.Support.ActiveFollowerDownAcceptance.RateInput

/-- The positive selected-DOWN credit made by one actual physical record. The
row is selected from the original `SourceInput`; the time and coordinator
feedback are retained by that record's successful physical step. -/
def recordPositiveDownCredit {p : Parameters} {rate : RateInput p}
    {source : BootstrapPrivateRoundStreams.SourceInput p}
    {rewards : ActualInitializationPhysicalStep.GridRewardTable p}
    (record : ActualInitializationRun.PhysicalRoundRecord p rate source rewards)
    (arm : Fin p.K) : ℕ :=
  if BootstrapCoordinatorLocalRound.downCreditArm p
      (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source))
      record.time
      (record.result.feedback (ActiveRoundActions.coordinator p.two_le_m)) = some arm
  then 1 else 0

/-- Per-arm total positive selected-DOWN credit in a chronological list of
actual records. -/
def recordsPositiveDownCredit {p : Parameters} {rate : RateInput p}
    {source : BootstrapPrivateRoundStreams.SourceInput p}
    {rewards : ActualInitializationPhysicalStep.GridRewardTable p}
    (records : List (ActualInitializationRun.PhysicalRoundRecord p rate source rewards))
    (arm : Fin p.K) : ℕ :=
  (records.map fun record => recordPositiveDownCredit record arm).sum

/-- A successful record's retained prepared coordinator input is exactly the
record's actual pre-round input. This identity is derived from `executed`. -/
theorem physicalRoundRecord_prepared_coordinatorInput
    {p : Parameters} {rate : RateInput p}
    {source : BootstrapPrivateRoundStreams.SourceInput p}
    {rewards : ActualInitializationPhysicalStep.GridRewardTable p}
    (record : ActualInitializationRun.PhysicalRoundRecord p rate source rewards) :
    record.result.prepared.coordinatorInput = record.coordinatorBefore := by
  have hready := (ActualInitializationPhysicalStep.step_succeeds_iff_ready rate
    record.block record.time record.coordinatorBefore record.followersBefore source rewards).mp
      ⟨record.result, record.executed⟩
  obtain ⟨prepared, hprepare⟩ :=
    (ActualInitializationPhysicalStep.prepare_eq_ok_iff_ready rate record.block record.time
      record.coordinatorBefore record.followersBefore source rewards).mpr hready
  have hstep : ActualInitializationPhysicalStep.observePrepared prepared = .ok record.result := by
    simpa [ActualInitializationPhysicalStep.step, hprepare] using record.executed
  have hresult : record.result.prepared = prepared := by
    have hround : record.result =
        ⟨prepared, (ActualInitializationPhysicalStep.observeFollowers prepared).val,
          (ActualInitializationPhysicalStep.observeFollowers prepared).property⟩ := by
      simpa [ActualInitializationPhysicalStep.observePrepared] using hstep.symm
    rw [hround]
  have hprepareInputs := hprepare
  simp [ActualInitializationPhysicalStep.prepare, hready] at hprepareInputs
  cases hprepareInputs
  rw [hresult]

/-- The successful prepared operation retains the original selected row and
the literal physical time of its record. -/
theorem physicalRoundRecord_selectedRow_time
    {p : Parameters} {rate : RateInput p}
    {source : BootstrapPrivateRoundStreams.SourceInput p}
    {rewards : ActualInitializationPhysicalStep.GridRewardTable p}
    (record : ActualInitializationRun.PhysicalRoundRecord p rate source rewards) :
    record.coordinatorBefore.data.row =
        source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) ∧
      record.result.prepared.time = record.time := by
  have hactual := ActualInitializationHorizon.physicalRoundRecord_actual record
  have hinput := physicalRoundRecord_prepared_coordinatorInput record
  have hselected : record.result.prepared.coordinatorInput.data.row =
      source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) := by
    simpa [hactual.2.1] using record.result.prepared.readiness.2.2.2.1
  constructor
  · rw [← hinput]
    exact hselected
  · exact record.result_time

/-- The actual coordinator continuation on a record applies exactly the
literal selected-row DOWN-positive counter update to its incoming monitor. -/
theorem physicalRoundRecord_nextMonitor_counters
    {p : Parameters} {rate : RateInput p}
    {source : BootstrapPrivateRoundStreams.SourceInput p}
    {rewards : ActualInitializationPhysicalStep.GridRewardTable p}
    (record : ActualInitializationRun.PhysicalRoundRecord p rate source rewards) :
    (record.result.coordinator.next).monitorState.counters =
      BootstrapCoordinatorLocalRound.countersAfterObservation p
        (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source))
        record.coordinatorBefore.monitor.1.counters record.time
        (record.result.feedback (ActiveRoundActions.coordinator p.two_le_m)) := by
  rw [ActualInitializationRun.roundResult_next_eq]
  rw [BootstrapCoordinatorLocalRound.continuationAfterObservation_monitor_counters]
  rw [physicalRoundRecord_prepared_coordinatorInput, record.result_time]
  rw [(physicalRoundRecord_selectedRow_time record).1]

/-- The record's post-observation counters are the incoming counters plus its
literal positive selected-DOWN credit, coordinate by coordinate. -/
theorem physicalRoundRecord_nextMonitor_credit
    {p : Parameters} {rate : RateInput p}
    {source : BootstrapPrivateRoundStreams.SourceInput p}
    {rewards : ActualInitializationPhysicalStep.GridRewardTable p}
    (record : ActualInitializationRun.PhysicalRoundRecord p rate source rewards)
    (arm : Fin p.K) :
    (record.result.coordinator.next).monitorState.counters arm =
      record.coordinatorBefore.monitor.1.counters arm +
        recordPositiveDownCredit record arm := by
  rw [physicalRoundRecord_nextMonitor_counters]
  rfl

/-- Credits split over the actual concatenation used by `runFrom`. -/
theorem recordsPositiveDownCredit_append {p : Parameters} {rate : RateInput p}
    {source : BootstrapPrivateRoundStreams.SourceInput p}
    {rewards : ActualInitializationPhysicalStep.GridRewardTable p}
    (left right : List (ActualInitializationRun.PhysicalRoundRecord p rate source rewards))
    (arm : Fin p.K) :
    recordsPositiveDownCredit (left ++ right) arm =
      recordsPositiveDownCredit left arm + recordsPositiveDownCredit right arm := by
  simp [recordsPositiveDownCredit, List.map_append, List.sum_append]

/-- The record credit sum exposes its first actual record. -/
theorem recordsPositiveDownCredit_cons {p : Parameters} {rate : RateInput p}
    {source : BootstrapPrivateRoundStreams.SourceInput p}
    {rewards : ActualInitializationPhysicalStep.GridRewardTable p}
    (record : ActualInitializationRun.PhysicalRoundRecord p rate source rewards)
    (records : List (ActualInitializationRun.PhysicalRoundRecord p rate source rewards))
    (arm : Fin p.K) :
    recordsPositiveDownCredit (record :: records) arm =
      recordPositiveDownCredit record arm + recordsPositiveDownCredit records arm := by
  simp [recordsPositiveDownCredit, List.map_cons]

/-- Induction over the existing `foldBlockAux`: its terminal continuation
monitor is the incoming monitor plus the positive selected-DOWN credits from
every actual record, including the final observation. -/
theorem foldBlockAux_counter_identity {p : Parameters} {rate : RateInput p}
    {block : Fin (n_boot p)} {source : BootstrapPrivateRoundStreams.SourceInput p}
    {rewards : ActualInitializationPhysicalStep.GridRewardTable p}
    {C_star C_h : ℝ} (cursor fuel : ℕ)
    (hbudget : cursor + fuel = BootstrapObservedFollower.blockLength p block)
    (phase : BootstrapCoordinatorLocalRound.Continuation p)
    (followers : Fin (p.m - 1) → ActualInitializationPhysicalStep.FollowerState p rate block)
    (hinvariant : ActualInitializationRun.BlockInvariant p rate block source C_star C_h
      cursor phase followers) :
    ∀ arm, (ActualInitializationRun.foldBlockAux p rate block source rewards C_star C_h
          cursor fuel hbudget phase followers hinvariant).phase.monitorState.counters arm =
      phase.monitorState.counters arm +
        recordsPositiveDownCredit
          (ActualInitializationRun.foldBlockAux p rate block source rewards C_star C_h
            cursor fuel hbudget phase followers hinvariant).records arm := by
  induction fuel generalizing cursor phase followers hinvariant with
  | zero =>
      simp [ActualInitializationRun.foldBlockAux, recordsPositiveDownCredit]
  | succ fuel ih =>
      have hcursor : cursor < BootstrapObservedFollower.blockLength p block := by omega
      cases phase with
      | launched launch =>
          have hdone := hinvariant.2.2.2
          omega
      | prelaunch coordinator =>
          simp only [ActualInitializationRun.foldBlockAux, recordsPositiveDownCredit_cons]
          intro arm
          refine Eq.trans (ih _ _ _ _ _ arm) ?_
          let time := ActualInitializationRun.blockTime p block cursor hcursor
          have htime : time ∈ BootstrapDimensions.calendarBlock p block := by
            exact ActualInitializationRun.blockTime_mem p block cursor hcursor
          have hready : ActualInitializationPhysicalStep.ActualInputReady p rate block time
              coordinator followers source := by
            refine ⟨hinvariant.1.1, htime, hinvariant.1.2.1,
              hinvariant.1.2.2.1, hinvariant.1.2.2.2.1, ?_⟩
            intro i
            cases hf : followers i with
            | bootstrap state =>
                have hc := hinvariant.2.2.1 i
                simp only [ActualInitializationRun.followerAtCursor, hf] at hc
                refine ⟨htime, ?_, ?_⟩
                · rw [hc]
                  exact hcursor
                · rw [hc]
                  rfl
            | declared row activation configuration =>
                have hc := hinvariant.2.2.1 i
                simp only [ActualInitializationRun.followerAtCursor, hf] at hc
                change activation.val ≤ time.val + 1
                simpa [time, ActualInitializationRun.blockTime] using hc
          have hcoordinatorTime : time ∈
              BootstrapDimensions.calendarBlock p coordinator.data.block := by
            have hdataBlock : coordinator.data.block = block := by
              simpa [ActualInitializationRun.continuationAligned,
                ActualInitializationRun.continuationData] using hinvariant.1.1
            rw [hdataBlock]
            exact htime
          let coordinatorPrepared := BootstrapCoordinatorLocalRound.prepare p coordinator time
            hcoordinatorTime
            (BootstrapPhysicalInput.playerRoundScalarAt p source.2
              (ActiveRoundActions.coordinator p.two_le_m) time)
          let prepared : ActualInitializationPhysicalStep.PreparedRound p rate block := {
            time := time
            source := source
            rewards := rewards
            coordinatorInput := coordinator
            followerInputs := followers
            readiness := hready
            coordinator := coordinatorPrepared
            coordinator_eq := rfl
            followers := fun i => ActualInitializationPhysicalStep.prepareFollowerValid rate
              block time source i (followers i) (hready.2.2.2.2.2 i)
            followers_eq := fun _ => rfl }
          have hprepare : ActualInitializationPhysicalStep.prepare rate block time coordinator
              followers source rewards = .ok prepared := by
            unfold ActualInitializationPhysicalStep.prepare
            simp [hready, prepared, coordinatorPrepared]
          let observed := ActualInitializationPhysicalStep.observeFollowers prepared
          let result : ActualInitializationPhysicalStep.RoundResult p rate block :=
            ⟨prepared, observed.val, observed.property⟩
          have hstep : ActualInitializationPhysicalStep.step rate block time coordinator
              followers source rewards = .ok result := by
            unfold ActualInitializationPhysicalStep.step
            simp [hprepare, result, ActualInitializationPhysicalStep.observePrepared, observed]
          let record : ActualInitializationRun.PhysicalRoundRecord p rate source rewards :=
            ⟨block, time, coordinator, followers, result, hstep, by simp [result, prepared]⟩
          have hcredit := physicalRoundRecord_nextMonitor_credit record arm
          rw [hcredit]
          simp only [recordPositiveDownCredit, record, result, prepared, observed,
            coordinatorPrepared, time, BootstrapCoordinatorLocalRound.Continuation.monitorState,
            Nat.add_assoc]

/-- A complete actual block adds precisely the selected-DOWN credits of its
physical records to the carried monitor counters. The accepted block-start
operation preserves the incoming monitor. -/
theorem foldBlock_counter_identity {p : Parameters} {rate : RateInput p}
    {block : Fin (n_boot p)} {source : BootstrapPrivateRoundStreams.SourceInput p}
    {rewards : ActualInitializationPhysicalStep.GridRewardTable p}
    (carry : ActualInitializationRun.BlockCarry p rate block) (arm : Fin p.K) :
    (ActualInitializationRun.foldBlock p rate block source rewards carry).phase.monitorState.counters arm =
      carry.monitor.1.counters arm +
        recordsPositiveDownCredit
          (ActualInitializationRun.foldBlock p rate block source rewards carry).records arm := by
  let started := ActualInitializationRun.beginBlock p rate block source carry
  have hbegin : started.coordinator.monitor.1.counters arm = carry.monitor.1.counters arm := by
    have hvector := BootstrapCoordinatorLocalRound.beginBlock_counters_preserved p block
      (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source))
      source.1.1 carry.coordinator carry.monitor carry.C_star carry.C_h
      (BootstrapPhysicalInput.coordinatorTargetScalarAt p block source.2)
    have hcoordinate := congrArg (fun counters : Fin p.K → ℕ => counters arm) hvector
    simpa [started, ActualInitializationRun.beginBlock,
      BootstrapPhysicalInput.coordinatorTargetScalarAt,
      ActualInitializationPhysicalStep.selectedRowIndex] using hcoordinate
  have haux := foldBlockAux_counter_identity (p := p) (rate := rate) (block := block)
    (source := source) (rewards := rewards) (C_star := carry.C_star) (C_h := carry.C_h)
    0 (BootstrapObservedFollower.blockLength p block) (by simp)
    (.prelaunch started.coordinator) started.followers started.invariant arm
  change (ActualInitializationRun.foldBlockAux p rate block source rewards carry.C_star carry.C_h
      0 (BootstrapObservedFollower.blockLength p block) (by simp)
      (.prelaunch started.coordinator) started.followers started.invariant).phase.monitorState.counters arm = _
  rw [BootstrapCoordinatorLocalRound.Continuation.monitorState, hbegin] at haux
  exact haux

/-- The first block of the computed actual execution starts from the literal
all-zero monitor, so its terminal counters are exactly its actual record
credits. -/
theorem foldInitialBlock_counter_identity {p : Parameters} {rate : RateInput p}
    {source : BootstrapPrivateRoundStreams.SourceInput p}
    {rewards : ActualInitializationPhysicalStep.GridRewardTable p}
    (C_star C_h : ℝ) (arm : Fin p.K) :
    (ActualInitializationRun.foldInitialBlock p rate source rewards C_star C_h).phase.monitorState.counters arm =
      recordsPositiveDownCredit
        (ActualInitializationRun.foldInitialBlock p rate source rewards C_star C_h).records arm := by
  have h := foldBlock_counter_identity (source := source) (rewards := rewards)
    (carry := ActualInitializationRun.initialCarry p rate C_star C_h) arm
  simpa [ActualInitializationRun.foldInitialBlock, ActualInitializationRun.initialCarry,
    ActualInitializationRun.initialUnlaunchedMonitor, ActualInitializationRun.firstBlock,
    BootstrapLaunchMonitor.initialState] using h

/-- The actual continued handoff carries precisely the monitor just computed
by the completed block. This follows from the `continueNext` equation, rather
than a separately supplied conservation property. -/
theorem combinedBoundaryHandoff_continueNext_monitor
    {p : Parameters} {rate : RateInput p} {block : Fin (n_boot p)}
    {source : BootstrapPrivateRoundStreams.SourceInput p}
    {rewards : ActualInitializationPhysicalStep.GridRewardTable p}
    {C_star C_h : ℝ}
    (folded : ActualInitializationRun.BlockFoldOutput p rate block source rewards
      C_star C_h 0)
    (next : Fin (n_boot p)) (nextCarry : ActualInitializationRun.BlockCarry p rate next)
    (h : (ActualInitializationRun.combinedBoundaryHandoff p rate block source rewards
      C_star C_h folded).disposition = .continueNext next nextCarry) :
    nextCarry.monitor.1 = folded.phase.monitorState := by
  obtain ⟨_, _, _, live, hphase, _, hmonitor, _⟩ :=
    ActualInitializationHorizon.combinedBoundaryHandoff_continueNext_facts
      folded next nextCarry h
  rw [hmonitor, hphase]
  rfl

-- Transport the dependent case analysis used by the accepted `runFrom` to
-- the constructor certified by its actual branch equation.
private theorem boundaryDisposition_casesOn_apply
    {p : Parameters} {rate : RateInput p} {block : Fin (n_boot p)} {α : Type*}
    (disposition : ActualInitializationRun.BoundaryDisposition p rate block)
    (continued : ∀ next nextCarry, disposition = .continueNext next nextCarry → α)
    (launched : ∀ launch learnerSeed, disposition = .launched launch learnerSeed → α)
    (exhausted : ∀ live, disposition = .exhausted live → α)
    {out : ActualInitializationRun.BoundaryDisposition p rate block}
    (h : disposition = out) :
    (ActualInitializationRun.BoundaryDisposition.casesOn
      (motive := fun d => disposition = d → α)
      disposition continued launched exhausted) rfl =
    (ActualInitializationRun.BoundaryDisposition.casesOn
      (motive := fun d => disposition = d → α)
      out continued launched exhausted) h := by
  cases h
  rfl

/-- Every actual suffix adds exactly the literal selected-DOWN credits in its
own chronological records to its incoming carry counters. The induction uses
the same remaining-block measure as `runFrom`; both terminal branches retain
the actual terminal fold, including its final physical observation. -/
theorem runFrom_counter_identity {p : Parameters} {rate : RateInput p}
    {source : BootstrapPrivateRoundStreams.SourceInput p}
    {rewards : ActualInitializationPhysicalStep.GridRewardTable p}
    {block : Fin (n_boot p)}
    (carry : ActualInitializationRun.BlockCarry p rate block) (arm : Fin p.K) :
    (ActualInitializationHorizon.runFrom p rate source rewards block carry).terminalFold.phase.monitorState.counters arm =
      carry.monitor.1.counters arm +
        recordsPositiveDownCredit
          (ActualInitializationHorizon.runFrom p rate source rewards block carry).records arm := by
  induction hremaining : n_boot p - block.val using Nat.strong_induction_on
      generalizing block with
  | h remaining ih =>
      cases hcontinue :
          (ActualInitializationRun.combinedBoundaryHandoff p rate block source rewards
            carry.C_star carry.C_h
            (ActualInitializationRun.foldBlock p rate block source rewards carry)).disposition with
      | continueNext next nextCarry =>
        rw [ActualInitializationHorizon.runFrom]
        rw [boundaryDisposition_casesOn_apply _ _ _ _ hcontinue]
        simp only [apply_eqRec (fun d _ =>
          (ActualInitializationRun.combinedBoundaryHandoff p rate block source rewards
            carry.C_star carry.C_h
            (ActualInitializationRun.foldBlock p rate block source rewards carry)).disposition = d)]
        rw [apply_eqRec (fun d _ =>
          (ActualInitializationRun.combinedBoundaryHandoff p rate block source rewards
            carry.C_star carry.C_h
            (ActualInitializationRun.foldBlock p rate block source rewards carry)).disposition = d)]
        have hmonitor := combinedBoundaryHandoff_continueNext_monitor
          (ActualInitializationRun.foldBlock p rate block source rewards carry)
          next nextCarry hcontinue
        have hdecrease := ActualInitializationHorizon.combinedBoundaryHandoff_remaining_decreases
          (ActualInitializationRun.foldBlock p rate block source rewards carry)
          next nextCarry hcontinue
        have htail := ih (n_boot p - next.val) (by omega) nextCarry rfl
        change (ActualInitializationHorizon.runFrom p rate source rewards next nextCarry).terminalFold.phase.monitorState.counters arm =
          carry.monitor.1.counters arm + recordsPositiveDownCredit
            ((ActualInitializationRun.foldBlock p rate block source rewards carry).records ++
              (ActualInitializationHorizon.runFrom p rate source rewards next nextCarry).records) arm
        rw [htail, hmonitor, foldBlock_counter_identity, recordsPositiveDownCredit_append]
        exact Nat.add_assoc _ _ _
      | launched launch learnerSeed =>
        rw [ActualInitializationHorizon.runFrom]
        rw [boundaryDisposition_casesOn_apply _ _ _ _ hcontinue]
        simp only [apply_eqRec (fun d _ =>
          (ActualInitializationRun.combinedBoundaryHandoff p rate block source rewards
            carry.C_star carry.C_h
            (ActualInitializationRun.foldBlock p rate block source rewards carry)).disposition = d)]
        rw [apply_eqRec (fun d _ =>
          (ActualInitializationRun.combinedBoundaryHandoff p rate block source rewards
            carry.C_star carry.C_h
            (ActualInitializationRun.foldBlock p rate block source rewards carry)).disposition = d)]
        exact foldBlock_counter_identity carry arm
      | exhausted live =>
        rw [ActualInitializationHorizon.runFrom]
        rw [boundaryDisposition_casesOn_apply _ _ _ _ hcontinue]
        simp only [apply_eqRec (fun d _ =>
          (ActualInitializationRun.combinedBoundaryHandoff p rate block source rewards
            carry.C_star carry.C_h
            (ActualInitializationRun.foldBlock p rate block source rewards carry)).disposition = d)]
        rw [apply_eqRec (fun d _ =>
          (ActualInitializationRun.combinedBoundaryHandoff p rate block source rewards
            carry.C_star carry.C_h
            (ActualInitializationRun.foldBlock p rate block source rewards carry)).disposition = d)]
        exact foldBlock_counter_identity carry arm

/-- Starting from the actual source initialization, every arm's terminal
counter is the sum of positive selected-DOWN credits in this run's own
concatenated chronological physical records. The initial carry contributes
zero; no separate trace, counter law, or launch premise is an input. -/
theorem sourceInitializedRun_counter_identity {p : Parameters} {rate : RateInput p}
    {source : BootstrapPrivateRoundStreams.SourceInput p}
    {rewards : ActualInitializationPhysicalStep.GridRewardTable p}
    (C_star C_h : ℝ) (arm : Fin p.K) :
    (ActualInitializationHorizon.sourceInitializedRun p rate source rewards
      C_star C_h).terminalFold.phase.monitorState.counters arm =
      recordsPositiveDownCredit
        (ActualInitializationHorizon.sourceInitializedRun p rate source rewards
          C_star C_h).records arm := by
  have h := runFrom_counter_identity (source := source) (rewards := rewards)
    (ActualInitializationRun.initialCarry p rate C_star C_h) arm
  simpa only [ActualInitializationHorizon.sourceInitializedRun,
    ActualInitializationRun.initialCarry, ActualInitializationRun.initialUnlaunchedMonitor,
    BootstrapLaunchMonitor.initialState, Nat.zero_add] using h

end Bandits.Support.ActualInitializationMonitorTrace

end
