/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ActualInitializationPhysicalStep
public import Bandits.Support.FirstAssignmentLaunch

import Lean.Elab.Tactic.Omega

/-!
# Actual chronological initialization blocks

This module starts actual bootstrap blocks from the original private scalar
coordinates and folds the accepted actual heterogeneous physical round in
strict calendar order.  At each completed clipped block it consumes the
accepted follower boundary operations and returns either the combined launch
handoff, the next block carry, or the honest horizon-exhaustion handoff.

The construction is an internal execution producer.  It makes no claim about
the source regret theorem, a probability coupling, or the postlaunch protocol.
Its first assignment learner seed follows
`sources/zip4/manuscript/04_slow_fast_learner.tex:193-195` and
`sources/zip4/manuscript/06_interruptions.tex:46-61`.
The source definitions are in `sources/zip4/manuscript/07_public_setup.tex:27-114`,
`sources/zip4/manuscript/appendix_b_communication.tex:94-165`,
`sources/zip4/manuscript/appendix_a_local_protocol.tex:6-14`, and
`sources/zip4/manuscript/06_interruptions.tex:108-114,235-297`.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.BootstrapObservedFollower
open Bandits.Support.BootstrapCoordinatorLocalRound
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.BootstrapPhysicalInput
open Bandits.Support.BootstrapPhysicalBlock
open Bandits.Support.BootstrapLaunchMonitor
open Bandits.Support.DeclaredFollowerLocalRound
open Bandits.Support.ReferencePrelaunchFollower
open Bandits.Support.ActiveFollowerLifecycle
open Bandits.Support.ActiveRoundActions
open Bandits.Support.ActualInitializationPhysicalStep
open Bandits.Support.ActiveFollowerDownAcceptance

namespace Bandits.Support.ActualInitializationRun

abbrev Parameters := ConstructorDimensions.Parameters

/-- One follower's boundary state.  The bootstrap branch retains its own
numerators; the declared branch retains its row, original activation, and full
ordinary or dagger configuration. -/
inductive FollowerCarry (p : Parameters) (rate : RateInput p) where
  | bootstrap (numerators : Fin p.K → ℕ)
      (lowerBound : ∀ a, 1 ≤ BootstrapWeightPotential.weight (b_N p) numerators a)
  | declared (row : Fin (M p)) (activation : ReferencePrelaunchFollower.Activation p)
      (configuration : DeclaredFollowerLocalRound.LocalConfiguration p rate)

/-- State carried into a particular block before its original block scalars
are consumed.  The activation bound says that each retained declaration has
taken effect by the first round of this block. -/
structure BlockCarry (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p)) where
  coordinator : BootstrapPhysicalBlock.State p
  monitor : BootstrapCoordinatorLocalRound.UnlaunchedMonitor p
  C_star : ℝ
  C_h : ℝ
  followers : Fin (p.m - 1) → FollowerCarry p rate
  activation_ready : ∀ i, match followers i with
    | .bootstrap _ _ => True
    | .declared _ activation _ =>
        activation.val ≤ BootstrapObservedFollower.blockStart p block + 1

/-- The first actual calendar block. -/
def firstBlock (p : Parameters) : Fin (n_boot p) :=
  ⟨0, BootstrapDimensions.n_boot_pos p⟩

/-- The monitor's exact source initial state with the no-launch sentinel. -/
def initialUnlaunchedMonitor (p : Parameters) :
    BootstrapCoordinatorLocalRound.UnlaunchedMonitor p := by
  exact ⟨BootstrapLaunchMonitor.initialState p, ⟨rfl, rfl⟩⟩

/-- The actual initial carry: zero coordinator counters and all-one bootstrap
numerators for every uninformed follower. -/
def initialCarry (p : Parameters) (rate : RateInput p) (C_star C_h : ℝ) :
    BlockCarry p rate (firstBlock p) where
  coordinator := BootstrapPhysicalBlock.initialState p
  monitor := initialUnlaunchedMonitor p
  C_star := C_star
  C_h := C_h
  followers := fun _ => .bootstrap (BootstrapObservedFollower.initialNumerators p)
    (BootstrapObservedFollower.initialNumerators_lower_bound p)
  activation_ready := by
    intro i
    simp

/-- The actual zero-based calendar round at offset `cursor` in a clipped
block.  Its domain is exactly the block's source rounds. -/
def blockTime (p : Parameters) (block : Fin (n_boot p)) (cursor : ℕ)
    (hcursor : cursor < BootstrapObservedFollower.blockLength p block) : Fin p.T := by
  have hstop : BootstrapObservedFollower.blockStart p block + cursor <
      BootstrapObservedFollower.blockStop p block := by
    have hstart := BootstrapObservedFollower.blockStart_lt_blockStop p block
    rw [BootstrapObservedFollower.blockLength] at hcursor
    omega
  have hT : BootstrapObservedFollower.blockStop p block ≤ p.T :=
    Nat.min_le_left _ _
  exact ⟨BootstrapObservedFollower.blockStart p block + cursor,
    lt_of_lt_of_le hstop hT⟩

/-- The block round at offset `cursor` belongs to the actual clipped block. -/
theorem blockTime_mem (p : Parameters) (block : Fin (n_boot p)) (cursor : ℕ)
    (hcursor : cursor < BootstrapObservedFollower.blockLength p block) :
    blockTime p block cursor hcursor ∈ BootstrapDimensions.calendarBlock p block := by
  rw [BootstrapDimensions.mem_calendarBlock_iff]
  constructor
  · exact Nat.le_add_right _ _
  · have hstart := BootstrapObservedFollower.blockStart_lt_blockStop p block
    rw [BootstrapObservedFollower.blockLength] at hcursor
    change BootstrapObservedFollower.blockStart p block + cursor <
      BootstrapObservedFollower.blockStop p block
    omega

/-- Exact chronological source times in a clipped block suffix. -/
def blockTimes (p : Parameters) (block : Fin (n_boot p)) (cursor fuel : ℕ)
    (hlength : cursor + fuel = BootstrapObservedFollower.blockLength p block) :
      List (Fin p.T) :=
  match fuel with
  | 0 => []
  | fuel + 1 =>
      blockTime p block cursor (by omega) ::
        blockTimes p block (cursor + 1) fuel (by omega)
termination_by fuel
decreasing_by omega

/-- All meaning-carrying coordinator fields agree with the original
published output and original private coordinates. -/
def continuationData (p : Parameters)
    (phase : BootstrapCoordinatorLocalRound.Continuation p) :
    BootstrapCoordinatorLocalRound.LocalData p :=
  match phase with
  | .prelaunch live => live.data
  | .launched launch => launch.data

/-- Update only the coordinator's block-local physical state. -/
def updateLocalCoordinatorState (p : Parameters)
    (data : BootstrapCoordinatorLocalRound.LocalData p)
    (state : BootstrapPhysicalBlock.State p) :
    BootstrapCoordinatorLocalRound.LocalData p :=
  { data with coordinator := state }

def continuationAligned (p : Parameters) (block : Fin (n_boot p))
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (C_star C_h : ℝ)
    (phase : BootstrapCoordinatorLocalRound.Continuation p) : Prop :=
  let data := continuationData p phase
  data.block = block ∧
    data.ids = source.1.1 ∧
    data.row = source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) ∧
    data.target = BootstrapPhysicalInput.targetArmMap p block source.2 ∧
    data.C_star = C_star ∧ data.C_h = C_h

/-- The accepted coordinator observation changes only its existing local
physical state inside the coordinator's retained block data. -/
theorem continuationAfterObservation_data (p : Parameters)
    (data : BootstrapCoordinatorLocalRound.LocalData p)
    (monitor : BootstrapCoordinatorLocalRound.UnlaunchedMonitor p)
    (coordinator : BootstrapPhysicalBlock.State p) (time : Fin p.T)
    (htime : time ∈ BootstrapDimensions.calendarBlock p data.block)
    (feedback : Fin (D p + 1)) :
    continuationData p (BootstrapCoordinatorLocalRound.continuationAfterObservation
      p data monitor coordinator time htime feedback) =
      updateLocalCoordinatorState p data
        (BootstrapCoordinatorLocalRound.observationUpdate p data.row data.ids coordinator
          time feedback) := by
  classical
  by_cases hcross : BootstrapCoordinatorLocalRound.launchTest p data monitor.1 time feedback
  · simp [continuationData, updateLocalCoordinatorState,
      BootstrapCoordinatorLocalRound.continuationAfterObservation, hcross]
  · simp [continuationData, updateLocalCoordinatorState,
      BootstrapCoordinatorLocalRound.continuationAfterObservation, hcross]

/-- A bootstrap state is at its own processed cursor; a declared state keeps
its original activation and is ready at this calendar offset. -/
def followerAtCursor (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p)) (cursor : ℕ)
    (follower : ActualInitializationPhysicalStep.FollowerState p rate block) : Prop :=
  match follower with
  | .bootstrap state => state.processed.val = cursor
  | .declared _ activation _ =>
      activation.val ≤ BootstrapObservedFollower.blockStart p block + cursor + 1

/-- Inductive state of the actual within-block execution.  The launched case
is confined to the real clipped endpoint. -/
def BlockInvariant (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p)) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (C_star C_h : ℝ) (cursor : ℕ) (phase : BootstrapCoordinatorLocalRound.Continuation p)
    (followers : Fin (p.m - 1) →
      ActualInitializationPhysicalStep.FollowerState p rate block) : Prop :=
  continuationAligned p block source C_star C_h phase ∧
    cursor ≤ BootstrapObservedFollower.blockLength p block ∧
    (∀ i, followerAtCursor p rate block cursor (followers i)) ∧
    (match phase with
      | .prelaunch _ => True
      | .launched _ => cursor = BootstrapObservedFollower.blockLength p block)

/-- The source-order block start uses each still-uninformed follower's own
carried numerators and original scalar triple. Declared followers are copied
whole. -/
def beginFollowerBlock (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p)) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) (carried : FollowerCarry p rate) :
      ActualInitializationPhysicalStep.FollowerState p rate block :=
  match carried with
  | .bootstrap numerators lowerBound =>
      .bootstrap (BootstrapObservedFollower.beginBlock p block numerators lowerBound
        (source.2.1.1 block i))
  | .declared row activation configuration =>
      .declared row activation configuration

/-- The complete actual first local state of a block. -/
structure StartedBlock (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p)) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (C_star C_h : ℝ) where
  coordinator : BootstrapCoordinatorLocalRound.PrelaunchBlock p
  followers : Fin (p.m - 1) → ActualInitializationPhysicalStep.FollowerState p rate block
  invariant : BlockInvariant p rate block source C_star C_h 0
    (.prelaunch coordinator) followers

/-- Begin the coordinator block from its carried counters and monitor, using
the original selected row, ID array, and target scalar. -/
def beginBlock (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p)) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (carried : BlockCarry p rate block) :
      StartedBlock p rate block source carried.C_star carried.C_h := by
  let coordinator := BootstrapCoordinatorLocalRound.beginBlock p block
    (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source))
    source.1.1 carried.coordinator carried.monitor carried.C_star carried.C_h
    (BootstrapPhysicalInput.coordinatorTargetScalarAt p block source.2)
  let followers := fun i =>
    beginFollowerBlock p rate block source i (carried.followers i)
  refine ⟨coordinator, followers, ?_⟩
  refine ⟨?_, Nat.zero_le _, ?_, trivial⟩
  · simp [continuationAligned, continuationData, coordinator,
      BootstrapCoordinatorLocalRound.beginBlock,
      ActualInitializationPhysicalStep.selectedRowIndex,
      BootstrapPhysicalInput.coordinatorTargetScalarAt,
      BootstrapPhysicalInput.targetArmMap]
  · intro i
    cases h : carried.followers i with
    | bootstrap numerators lowerBound =>
        simp only [followerAtCursor, followers, beginFollowerBlock, h]
        unfold BootstrapObservedFollower.beginBlock
        by_cases hactive : PrivateSourceStreams.activityScalarDraw p
            (source.2.1.1 block i).1 = true <;> simp [hactive]
    | declared row activation configuration =>
        simpa [followerAtCursor, followers, beginFollowerBlock, h] using
          carried.activation_ready i

/-- The exact finite action and joint feedback record produced by an actual
physical step. Its proof field certifies that the accepted `step` consumed the
recorded pre-round coordinator and follower states. -/
structure PhysicalRoundRecord (p : Parameters) (rate : RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) where
  block : Fin (n_boot p)
  time : Fin p.T
  coordinatorBefore : BootstrapCoordinatorLocalRound.PrelaunchBlock p
  followersBefore : Fin (p.m - 1) →
    ActualInitializationPhysicalStep.FollowerState p rate block
  result : ActualInitializationPhysicalStep.RoundResult p rate block
  executed : ActualInitializationPhysicalStep.step rate block time coordinatorBefore
    followersBefore source rewards = .ok result
  result_time : result.prepared.time = time

/-- Literal times in a record list. -/
def PhysicalRoundRecord.times {p : Parameters} {rate : RateInput p}
    {source : BootstrapPrivateRoundStreams.SourceInput p}
    {rewards : ActualInitializationPhysicalStep.GridRewardTable p}
    (records : List (PhysicalRoundRecord p rate source rewards)) : List (Fin p.T) :=
  records.map PhysicalRoundRecord.time

/-- Actual finite physical action history, derived from the accepted round
results rather than supplied as an input. -/
def PhysicalRoundRecord.actions {p : Parameters} {rate : RateInput p}
    {source : BootstrapPrivateRoundStreams.SourceInput p}
    {rewards : ActualInitializationPhysicalStep.GridRewardTable p}
    (records : List (PhysicalRoundRecord p rate source rewards)) :
      List (FiniteBanditModel.ActionProfile p.m p.K) :=
  records.map fun record => record.result.actions

/-- Actual finite joint feedback history, derived from the same simultaneous
physical rounds as the action history. -/
def PhysicalRoundRecord.feedback {p : Parameters} {rate : RateInput p}
    {source : BootstrapPrivateRoundStreams.SourceInput p}
    {rewards : ActualInitializationPhysicalStep.GridRewardTable p}
    (records : List (PhysicalRoundRecord p rate source rewards)) :
      List (Fin p.m → Fin (D p + 1)) :=
  records.map fun record => record.result.feedback

/-- The within-block fold returns the actual last continuation, every
post-observation follower state, and the records of precisely its suffix. -/
structure BlockFoldOutput (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p)) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (cursor : ℕ) where
  consumed : ℕ
  phase : BootstrapCoordinatorLocalRound.Continuation p
  followers : Fin (p.m - 1) → ActualInitializationPhysicalStep.FollowerState p rate block
  records : List (PhysicalRoundRecord p rate source rewards)
  invariant : BlockInvariant p rate block source C_star C_h consumed phase followers
  consumed_eq_blockLength : consumed = BootstrapObservedFollower.blockLength p block
  record_count : records.length + cursor = consumed
  chronological : PhysicalRoundRecord.times records =
    blockTimes p block cursor records.length (by omega)

/-- The coordinator continuation in a successful physical result is the
accepted observation of the exact prepared coordinator round. -/
theorem roundResult_next_eq {p : Parameters} {rate : RateInput p}
    {block : Fin (n_boot p)} (result : ActualInitializationPhysicalStep.RoundResult p rate block) :
    result.coordinator.next =
      BootstrapCoordinatorLocalRound.continuationAfterObservation p
        result.prepared.coordinatorInput.data result.prepared.coordinatorInput.monitor
        result.prepared.coordinatorInput.data.coordinator result.prepared.time
        (by rw [result.prepared.readiness.1]; exact result.prepared.readiness.2.1)
        (result.feedback (ActiveRoundActions.coordinator p.two_le_m)) := by
  unfold ActualInitializationPhysicalStep.RoundResult.coordinator
  rw [result.prepared.coordinator_eq]
  rfl

theorem continuationAfterObservation_launched_trigger {p : Parameters}
    (data : BootstrapCoordinatorLocalRound.LocalData p)
    (monitor : BootstrapCoordinatorLocalRound.UnlaunchedMonitor p)
    (coordinator : BootstrapPhysicalBlock.State p) (time : Fin p.T)
    (htime : time ∈ BootstrapDimensions.calendarBlock p data.block)
    (feedback : Fin (D p + 1)) (launch : BootstrapCoordinatorLocalRound.LaunchedBlock p)
    (hphase : BootstrapCoordinatorLocalRound.continuationAfterObservation p data monitor
      coordinator time htime feedback = .launched launch) :
    launch.triggerRound = time := by
  classical
  by_cases hcross : BootstrapCoordinatorLocalRound.launchTest p data monitor.1 time feedback
  · simp [BootstrapCoordinatorLocalRound.continuationAfterObservation, hcross] at hphase
    exact (congrArg BootstrapCoordinatorLocalRound.LaunchedBlock.triggerRound hphase).symm
  · simp [BootstrapCoordinatorLocalRound.continuationAfterObservation, hcross] at hphase

theorem prepareFollowerValid_congr {p : Parameters} {rate : RateInput p}
    {block : Fin (n_boot p)} (time : Fin p.T)
    (source : BootstrapPrivateRoundStreams.SourceInput p) (i : Fin (p.m - 1))
    (left right : ActualInitializationPhysicalStep.FollowerState p rate block)
    (heq : left = right)
    (hleft : ActualInitializationPhysicalStep.followerAtNextCursor time left)
    (hright : ActualInitializationPhysicalStep.followerAtNextCursor time right) :
    ActualInitializationPhysicalStep.prepareFollowerValid rate block time source i left hleft =
      ActualInitializationPhysicalStep.prepareFollowerValid rate block time source i right hright := by
  cases heq
  rfl

/-- One completed clipped block's actual rounds, before its boundary adapter.
The recursion consumes exactly the accepted per-round output and carries the
coordinator continuation and every heterogeneous follower state forward. -/
noncomputable def foldBlockAux (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p)) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (cursor fuel : ℕ) (hbudget : cursor + fuel =
      BootstrapObservedFollower.blockLength p block)
    (phase : BootstrapCoordinatorLocalRound.Continuation p)
    (followers : Fin (p.m - 1) →
      ActualInitializationPhysicalStep.FollowerState p rate block)
    (hinvariant : BlockInvariant p rate block source C_star C_h cursor phase followers) :
      BlockFoldOutput p rate block source rewards C_star C_h cursor := by
  classical
  cases fuel with
  | zero =>
      have hcursor : cursor = BootstrapObservedFollower.blockLength p block := by
        simpa using hbudget
      refine ⟨cursor, phase, followers, [], ?_, ?_, ?_, ?_⟩
      · exact hinvariant
      · exact hcursor
      · simp
      · simp [PhysicalRoundRecord.times, blockTimes]
  | succ fuel =>
      have hcursor : cursor < BootstrapObservedFollower.blockLength p block := by
        omega
      have htime : blockTime p block cursor hcursor ∈
          BootstrapDimensions.calendarBlock p block :=
        blockTime_mem p block cursor hcursor
      cases phase with
      | launched launch =>
          have hdone := hinvariant.2.2.2
          omega
      | prelaunch coordinator =>
          have hready : ActualInitializationPhysicalStep.ActualInputReady p rate block
              (blockTime p block cursor hcursor) coordinator followers source := by
            refine ⟨hinvariant.1.1, htime, hinvariant.1.2.1,
              hinvariant.1.2.2.1, hinvariant.1.2.2.2.1, ?_⟩
            intro i
            cases hf : followers i with
            | bootstrap state =>
                have hc := hinvariant.2.2.1 i
                simp only [followerAtCursor, hf] at hc
                refine ⟨htime, ?_, ?_⟩
                · rw [hc]
                  exact hcursor
                · rw [hc]
                  rfl
            | declared row activation configuration =>
                have hc := hinvariant.2.2.1 i
                simp only [followerAtCursor, hf] at hc
                change activation.val ≤ (blockTime p block cursor hcursor).val + 1
                simpa [blockTime] using hc
          have hcoordinatorTime : (blockTime p block cursor hcursor) ∈
              BootstrapDimensions.calendarBlock p coordinator.data.block := by
            have hdataBlock : coordinator.data.block = block := by
                simpa [continuationAligned, continuationData] using hinvariant.1.1
            rw [hdataBlock]
            exact htime
          let coordinatorPrepared := BootstrapCoordinatorLocalRound.prepare p coordinator
            (blockTime p block cursor hcursor) hcoordinatorTime
            (BootstrapPhysicalInput.playerRoundScalarAt p source.2
              (ActiveRoundActions.coordinator p.two_le_m)
              (blockTime p block cursor hcursor))
          let prepared : ActualInitializationPhysicalStep.PreparedRound p rate block := {
            time := blockTime p block cursor hcursor
            source := source
            rewards := rewards
            coordinatorInput := coordinator
            followerInputs := followers
            readiness := hready
            coordinator := coordinatorPrepared
            coordinator_eq := rfl
            followers := fun i => ActualInitializationPhysicalStep.prepareFollowerValid rate
              block (blockTime p block cursor hcursor) source i (followers i)
              (hready.2.2.2.2.2 i)
            followers_eq := fun _ => rfl }
          have hprepare : ActualInitializationPhysicalStep.prepare rate block
              (blockTime p block cursor hcursor) coordinator followers source rewards =
                .ok prepared := by
            unfold ActualInitializationPhysicalStep.prepare
            simp [hready, prepared, coordinatorPrepared]
          let observed := ActualInitializationPhysicalStep.observeFollowers prepared
          let result : ActualInitializationPhysicalStep.RoundResult p rate block :=
            ⟨prepared, observed.val, observed.property⟩
          have hstep : ActualInitializationPhysicalStep.step rate block
              (blockTime p block cursor hcursor) coordinator followers source rewards =
                .ok result := by
            unfold ActualInitializationPhysicalStep.step
            simp [hprepare, result, ActualInitializationPhysicalStep.observePrepared,
              observed]
          let followers' := fun i => (result.followers i).next
          have hinvariant' : BlockInvariant p rate block source C_star C_h (cursor + 1)
              result.coordinator.next followers' := by
            refine ⟨?_, ?_, ?_, ?_⟩
            · have hnextEq := roundResult_next_eq result
              have hdata : continuationData p result.coordinator.next =
                  updateLocalCoordinatorState p coordinator.data
                    (BootstrapCoordinatorLocalRound.observationUpdate p coordinator.data.row
                      coordinator.data.ids coordinator.data.coordinator
                      (blockTime p block cursor hcursor)
                      (result.feedback (ActiveRoundActions.coordinator p.two_le_m))) := by
                rw [hnextEq]
                simpa [result, prepared] using
                  continuationAfterObservation_data p coordinator.data coordinator.monitor
                    coordinator.data.coordinator (blockTime p block cursor hcursor)
                    hcoordinatorTime
                    (result.feedback (ActiveRoundActions.coordinator p.two_le_m))
              change
                (continuationData p result.coordinator.next).block = block ∧
                  (continuationData p result.coordinator.next).ids = source.1.1 ∧
                  (continuationData p result.coordinator.next).row =
                    source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) ∧
                  (continuationData p result.coordinator.next).target =
                    BootstrapPhysicalInput.targetArmMap p block source.2 ∧
                  (continuationData p result.coordinator.next).C_star = C_star ∧
                  (continuationData p result.coordinator.next).C_h = C_h
              have hAligned : coordinator.data.block = block ∧
                  coordinator.data.ids = source.1.1 ∧
                  coordinator.data.row = source.1.2
                    (ActualInitializationPhysicalStep.selectedRowIndex p source) ∧
                  coordinator.data.target = BootstrapPhysicalInput.targetArmMap p block source.2 ∧
                  coordinator.data.C_star = C_star ∧ coordinator.data.C_h = C_h := by
                simpa [continuationAligned, continuationData] using hinvariant.1
              have hAligned' :
                  (continuationData p result.coordinator.next).block = block ∧
                    (continuationData p result.coordinator.next).ids = source.1.1 ∧
                    (continuationData p result.coordinator.next).row = source.1.2
                      (ActualInitializationPhysicalStep.selectedRowIndex p source) ∧
                    (continuationData p result.coordinator.next).target =
                      BootstrapPhysicalInput.targetArmMap p block source.2 ∧
                    (continuationData p result.coordinator.next).C_star = C_star ∧
                    (continuationData p result.coordinator.next).C_h = C_h := by
                rw [hdata]
                simpa [updateLocalCoordinatorState] using hAligned
              exact hAligned'
            · omega
            · intro i
              cases hf : followers i with
              | bootstrap state =>
                  have hc := hinvariant.2.2.1 i
                  simp only [followerAtCursor, hf] at hc
                  have hnext := result.followerTransition i
                  let arm := BootstrapObservedFollower.localArm p block state source.1.1
                    (blockTime p block cursor hcursor)
                    (fun t => BootstrapPhysicalInput.playerRoundScalarAt p source.2
                      (PublicDiscreteDraws.followerPlayer p.two_le_m i) t)
                  have hprepared' : result.prepared.followers i = .bootstrap state arm := by
                    have hreadyI := hready.2.2.2.2.2 i
                    have hreadyState : ActualInitializationPhysicalStep.followerAtNextCursor
                        (blockTime p block cursor hcursor)
                        (.bootstrap state : ActualInitializationPhysicalStep.FollowerState p rate block) := by
                      simpa [hf] using hreadyI
                    have hfield : result.prepared.followers i =
                        ActualInitializationPhysicalStep.prepareFollowerValid rate block
                          (blockTime p block cursor hcursor) source i (followers i) hreadyI := by
                      rfl
                    have hcongr := prepareFollowerValid_congr
                      (blockTime p block cursor hcursor) source i (followers i)
                      (.bootstrap state : ActualInitializationPhysicalStep.FollowerState p rate block)
                      hf hreadyI hreadyState
                    have hbranch :
                        ActualInitializationPhysicalStep.prepareFollowerValid rate block
                          (blockTime p block cursor hcursor) source i
                          (.bootstrap state : ActualInitializationPhysicalStep.FollowerState p rate block)
                          hreadyState =
                            .bootstrap state arm := by
                      rfl
                    exact hfield.trans (hcongr.trans hbranch)
                  have hopen : state.processed.val < BootstrapObservedFollower.blockLength p block := by
                    rw [hc]
                    exact hcursor
                  have hcurrent : (blockTime p block cursor hcursor).val =
                      BootstrapObservedFollower.blockStart p block + state.processed.val := by
                    rw [hc]
                    rfl
                  let ownFeedback := result.feedback
                    (PublicDiscreteDraws.followerPlayer p.two_le_m i)
                  let next := BootstrapObservedFollower.observeOne p block state source.1.1
                    source.1.2 (blockTime p block cursor hcursor)
                    (ActualInitializationPhysicalStep.observationOfGrid p ownFeedback)
                    htime hopen hcurrent
                  have hobs := BootstrapObservedFollower.observe_accepted_processed p block state
                    source.1.1 source.1.2 (blockTime p block cursor hcursor)
                    (ActualInitializationPhysicalStep.observationOfGrid p ownFeedback)
                    htime hopen hcurrent
                  have hstartup :=
                    ActualInitializationPhysicalStep.observeFollower_bootstrap_next_is_startup
                      rate block (blockTime p block cursor hcursor) source i state next arm
                      ownFeedback hobs
                  have hstate : (result.followers i).next = .bootstrap next := by
                    rw [hprepared'] at hnext
                    have hnext' : observeFollower rate block
                        (blockTime p block cursor hcursor) source i
                        (.bootstrap state arm) ownFeedback = .ok (result.followers i) := by
                      simpa [result, prepared, ownFeedback,
                        ActualInitializationPhysicalStep.RoundResult.feedback] using hnext
                    rw [hstartup] at hnext'
                    exact congrArg FollowerOutcome.next (Except.ok.inj hnext').symm
                  change followerAtCursor p rate block (cursor + 1)
                    ((result.followers i).next)
                  rw [hstate]
                  change next.processed.val = cursor + 1
                  have hprocessed := BootstrapObservedFollower.observe_accepted_cursor p block
                    state source.1.1 source.1.2 (blockTime p block cursor hcursor)
                    (ActualInitializationPhysicalStep.observationOfGrid p ownFeedback)
                    htime hopen hcurrent
                  rw [hprocessed, hc]
              | declared row activation configuration =>
                  have hc := hinvariant.2.2.1 i
                  simp only [followerAtCursor, hf] at hc
                  have hactive : activation.val ≤ (blockTime p block cursor hcursor).val + 1 := by
                    simpa [blockTime] using hc
                  have hprepared' : result.prepared.followers i =
                      .declared row activation
                        (DeclaredFollowerLocalRound.prepare rate i (source.1.2 row) activation
                          (blockTime p block cursor hcursor) hactive configuration) := by
                    have hreadyI := hready.2.2.2.2.2 i
                    have hreadyState : ActualInitializationPhysicalStep.followerAtNextCursor
                        (blockTime p block cursor hcursor)
                        (.declared row activation configuration :
                          ActualInitializationPhysicalStep.FollowerState p rate block) := by
                      simpa [hf] using hreadyI
                    have hfield : result.prepared.followers i =
                        ActualInitializationPhysicalStep.prepareFollowerValid rate block
                          (blockTime p block cursor hcursor) source i (followers i) hreadyI := by
                      rfl
                    have hcongr := prepareFollowerValid_congr
                      (blockTime p block cursor hcursor) source i (followers i)
                      (.declared row activation configuration :
                        ActualInitializationPhysicalStep.FollowerState p rate block)
                      hf hreadyI hreadyState
                    have hbranch :
                        ActualInitializationPhysicalStep.prepareFollowerValid rate block
                          (blockTime p block cursor hcursor) source i
                          (.declared row activation configuration :
                            ActualInitializationPhysicalStep.FollowerState p rate block) hreadyState =
                            .declared row activation
                              (DeclaredFollowerLocalRound.prepare rate i (source.1.2 row)
                                activation (blockTime p block cursor hcursor) hactive configuration) := by
                      rfl
                    exact hfield.trans (hcongr.trans hbranch)
                  have hnext := result.followerTransition i
                  rw [hprepared'] at hnext
                  let round := DeclaredFollowerLocalRound.prepare rate i
                    (source.1.2 row) activation (blockTime p block cursor hcursor)
                    hactive configuration
                  have hdeclared :=
                    ActualInitializationPhysicalStep.observeFollower_declared_eq
                      rate block (blockTime p block cursor hcursor) source i row activation
                      round (result.feedback
                        (PublicDiscreteDraws.followerPlayer p.two_le_m i))
                  have hnext' : observeFollower rate block
                      (blockTime p block cursor hcursor) source i (.declared row activation round)
                      (result.feedback (PublicDiscreteDraws.followerPlayer p.two_le_m i)) =
                        .ok (result.followers i) := by
                    simpa [result, prepared,
                      ActualInitializationPhysicalStep.RoundResult.feedback] using hnext
                  have hstate := congrArg FollowerOutcome.next
                    (Except.ok.inj (hdeclared.symm.trans hnext'))
                  change followerAtCursor p rate block (cursor + 1)
                    ((result.followers i).next)
                  rw [← hstate]
                  simp only [followerAtCursor]
                  omega
            · cases hphase : result.coordinator.next with
              | prelaunch live => trivial
              | launched launch =>
                  have hnextEq := roundResult_next_eq result
                  have hphaseObs : BootstrapCoordinatorLocalRound.continuationAfterObservation p
                      coordinator.data coordinator.monitor coordinator.data.coordinator
                      (blockTime p block cursor hcursor) hcoordinatorTime
                      (result.feedback (ActiveRoundActions.coordinator p.two_le_m)) =
                        .launched launch := by
                    simpa [result, prepared] using hnextEq.symm.trans hphase
                  have hlaunchData : launch.data =
                      updateLocalCoordinatorState p coordinator.data
                        (BootstrapCoordinatorLocalRound.observationUpdate p
                          coordinator.data.row coordinator.data.ids coordinator.data.coordinator
                          (blockTime p block cursor hcursor)
                          (result.feedback (ActiveRoundActions.coordinator p.two_le_m))) := by
                    have hdata := continuationAfterObservation_data p coordinator.data
                      coordinator.monitor coordinator.data.coordinator
                      (blockTime p block cursor hcursor) hcoordinatorTime
                      (result.feedback (ActiveRoundActions.coordinator p.two_le_m))
                    rw [hphaseObs] at hdata
                    simpa [continuationData] using hdata
                  have hlaunchBlock : launch.data.block = block := by
                    have hblock := congrArg
                      (fun data : BootstrapCoordinatorLocalRound.LocalData p => data.block)
                      hlaunchData
                    simpa [updateLocalCoordinatorState] using hblock.trans hinvariant.1.1
                  have htrigger := continuationAfterObservation_launched_trigger
                    coordinator.data coordinator.monitor coordinator.data.coordinator
                    (blockTime p block cursor hcursor) hcoordinatorTime
                    (result.feedback (ActiveRoundActions.coordinator p.two_le_m)) launch hphaseObs
                  have hlaunchInBlock : launch.triggerRound ∈
                      BootstrapDimensions.calendarBlock p block := by
                    rw [← hlaunchBlock]
                    exact launch.triggerInBlock
                  have hquot := (BootstrapDimensions.mem_calendarBlock_iff_quotient p block
                    launch.triggerRound).1 hlaunchInBlock
                  have hindex : BootstrapDimensions.roundBlockIndex p
                      (blockTime p block cursor hcursor) = block := by
                    apply Fin.ext
                    change (blockTime p block cursor hcursor).val / B_boot p = block.val
                    rw [← htrigger]
                    exact hquot.symm
                  have hendpoint := launch.triggerAtBlockEnd
                  unfold BootstrapLaunchMonitor.calendarBlockEnd at hendpoint
                  rw [htrigger, hindex, BootstrapDimensions.manuscriptRound] at hendpoint
                  have hend : launch.triggerRound.val + 1 =
                      BootstrapObservedFollower.blockStop p block := by
                    rw [htrigger, BootstrapObservedFollower.blockStop]
                    exact hendpoint
                  have htimeval := congrArg Fin.val htrigger
                  simp only [blockTime] at htimeval
                  have hstartstop : BootstrapObservedFollower.blockStart p block +
                      BootstrapObservedFollower.blockLength p block =
                        BootstrapObservedFollower.blockStop p block := by
                    have hle := Nat.le_of_lt
                      (BootstrapObservedFollower.blockStart_lt_blockStop p block)
                    unfold BootstrapObservedFollower.blockLength
                    omega
                  rw [htimeval, ← hstartstop] at hend
                  omega
          let record : PhysicalRoundRecord p rate source rewards :=
            ⟨block, blockTime p block cursor hcursor, coordinator,
              followers, result, hstep, by simp [result, prepared]⟩
          let tail := foldBlockAux p rate block source rewards C_star C_h (cursor + 1) fuel
            (by omega) result.coordinator.next followers' hinvariant'
          refine ⟨tail.consumed, tail.phase, tail.followers,
            record :: tail.records, tail.invariant,
            tail.consumed_eq_blockLength, ?_, ?_⟩
          · simp only [List.length_cons]
            have := tail.record_count
            omega
          · simp only [PhysicalRoundRecord.times, List.map_cons, List.length_cons, blockTimes]
            change record.time :: PhysicalRoundRecord.times tail.records = _
            have htailBudget : cursor + 1 + tail.records.length =
                BootstrapObservedFollower.blockLength p block := by
              have h := tail.record_count
              rw [tail.consumed_eq_blockLength] at h
              omega
            calc
              record.time :: PhysicalRoundRecord.times tail.records =
                  blockTime p block cursor hcursor :: PhysicalRoundRecord.times tail.records := by
                    rfl
              _ = blockTime p block cursor hcursor ::
                    blockTimes p block (cursor + 1) tail.records.length htailBudget :=
                  congrArg (List.cons (blockTime p block cursor hcursor)) tail.chronological

/-- Execute one actual clipped block from its carried coordinator, monitor,
and heterogeneous follower states.  The block starts from the original
source scalar coordinates and the accepted block-start operations. -/
noncomputable def foldBlock (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p)) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (carry : BlockCarry p rate block) :
      BlockFoldOutput p rate block source rewards carry.C_star carry.C_h 0 := by
  let started := beginBlock p rate block source carry
  exact foldBlockAux p rate block source rewards carry.C_star carry.C_h 0
    (BootstrapObservedFollower.blockLength p block) (by simp)
    (.prelaunch started.coordinator) started.followers started.invariant

/-- The first actual clipped block begins from the source initial numerators,
zero coordinator state, and the all-zero unlaunched monitor. -/
noncomputable def foldInitialBlock (p : Parameters) (rate : RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) :
      BlockFoldOutput p rate (firstBlock p) source rewards C_star C_h 0 :=
  foldBlock p rate (firstBlock p) source rewards (initialCarry p rate C_star C_h)

/-- The end-of-block invariant gives each bootstrap follower its own exact
completed cursor. -/
theorem blockFold_follower_complete {p : Parameters} {rate : RateInput p}
    {block : Fin (n_boot p)} {source : BootstrapPrivateRoundStreams.SourceInput p}
    {rewards : ActualInitializationPhysicalStep.GridRewardTable p}
    {C_star C_h : ℝ} {cursor : ℕ}
    (folded : BlockFoldOutput p rate block source rewards C_star C_h cursor)
    (i : Fin (p.m - 1)) :
    followerAtCursor p rate block (BootstrapObservedFollower.blockLength p block)
      (folded.followers i) := by
  have h := folded.invariant.2.2.1 i
  rw [folded.consumed_eq_blockLength] at h
  exact h

/-- The full block's public action and joint feedback histories each contain
exactly one entry for every processed calendar round. -/
theorem blockFold_history_lengths {p : Parameters} {rate : RateInput p}
    {block : Fin (n_boot p)} {source : BootstrapPrivateRoundStreams.SourceInput p}
    {rewards : ActualInitializationPhysicalStep.GridRewardTable p}
    {C_star C_h : ℝ}
    (folded : BlockFoldOutput p rate block source rewards C_star C_h 0) :
    (PhysicalRoundRecord.actions folded.records).length =
        BootstrapObservedFollower.blockLength p block ∧
      (PhysicalRoundRecord.feedback folded.records).length =
        BootstrapObservedFollower.blockLength p block := by
  have hcount := folded.record_count
  rw [folded.consumed_eq_blockLength] at hcount
  constructor <;>
    simp only [PhysicalRoundRecord.actions, PhysicalRoundRecord.feedback,
      List.length_map] <;>
    omega

/-- The exact half-open interval identity used when carried declarations
enter the following source block. -/
theorem blockStart_add_length_eq_stop (p : Parameters) (block : Fin (n_boot p)) :
    BootstrapObservedFollower.blockStart p block +
      BootstrapObservedFollower.blockLength p block =
        BootstrapObservedFollower.blockStop p block := by
  unfold BootstrapObservedFollower.blockLength
  exact Nat.add_sub_of_le (Nat.le_of_lt
    (BootstrapObservedFollower.blockStart_lt_blockStop p block))

/-- The next source block when the current block is not the clipped last
block. -/
def successorBlock (p : Parameters) (block : Fin (n_boot p))
    (hnext : block.val + 1 < n_boot p) : Fin (n_boot p) :=
  ⟨block.val + 1, hnext⟩

private theorem nextActivation_le_successorStart (p : Parameters)
    (block : Fin (n_boot p)) (hnext : block.val + 1 < n_boot p) :
    (BootstrapObservedFollower.nextActivationRound p block).val ≤
      BootstrapObservedFollower.blockStart p (successorBlock p block hnext) + 1 := by
  have heq : (BootstrapObservedFollower.nextActivationRound p block).val =
      BootstrapObservedFollower.blockStart p (successorBlock p block hnext) + 1 := by
    simpa [successorBlock, BootstrapObservedFollower.blockStart] using
      BootstrapObservedFollower.nextActivationRound_nonlast_eq_nextStart p block hnext
  exact le_of_eq heq

private theorem stop_eq_successorStart (p : Parameters)
    (block : Fin (n_boot p)) (hnext : block.val + 1 < n_boot p) :
    BootstrapObservedFollower.blockStop p block =
      BootstrapObservedFollower.blockStart p (successorBlock p block hnext) := by
  have hactivation : (BootstrapObservedFollower.nextActivationRound p block).val =
      BootstrapObservedFollower.blockStart p (successorBlock p block hnext) + 1 := by
    simpa [successorBlock, BootstrapObservedFollower.blockStart] using
      BootstrapObservedFollower.nextActivationRound_nonlast_eq_nextStart p block hnext
  change BootstrapObservedFollower.blockStop p block + 1 = _ at hactivation
  omega

/-- The literal follower boundary output. Bootstrap finish uses the accepted
full-block update; declared followers are copied intact. -/
noncomputable def boundaryOutputFromFollower (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p))
    (follower : ActualInitializationPhysicalStep.FollowerState p rate block) :
      ActualInitializationPhysicalStep.BoundaryFollowerOutput p rate :=
  match follower with
  | .bootstrap state =>
      (BootstrapObservedFollower.pendingDeclaration state.blockCase).elim
        (.continueBootstrap
          (BootstrapObservedFollower.updatedNumerators p block state)
          (BootstrapObservedFollower.updatedNumerators_lower_bound p block state)
          (BootstrapObservedFollower.nextActivationRound p block))
        (fun row => .firstDeclaration row
          (BootstrapObservedFollower.nextActivationRound p block)
          (ReferencePrelaunchFollower.initial p rate.eta)
          (ActiveFollowerLifecycle.initialMemory p))
  | .declared row activation configuration => .preserveDeclared row activation configuration

/-- The literal boundary output at a completed own-observation cursor. -/
def boundaryOutputAtCursor (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p))
    (follower : ActualInitializationPhysicalStep.FollowerState p rate block)
    (_hcomplete : followerAtCursor p rate block
      (BootstrapObservedFollower.blockLength p block) follower) :
      ActualInitializationPhysicalStep.BoundaryFollowerOutput p rate :=
  boundaryOutputFromFollower p rate block follower

/-- A bootstrap follower's first declaration or continuation on the clipped
last block carries the exact terminal activation `T + 1`. -/
theorem bootstrapBoundaryOutput_finalActivation {p : Parameters} {rate : RateInput p}
    {block : Fin (n_boot p)} (state : BootstrapObservedFollower.StartupState p block)
    (hlast : block.val + 1 = n_boot p) :
    match boundaryOutputFromFollower p rate block (.bootstrap state) with
    | .continueBootstrap _ _ activation => activation.val = p.T + 1
    | .firstDeclaration _ activation _ _ => activation.val = p.T + 1
    | .preserveDeclared _ _ _ => True := by
  cases hpending : BootstrapObservedFollower.pendingDeclaration state.blockCase with
  | none =>
      simp [boundaryOutputFromFollower, hpending,
        BootstrapObservedFollower.nextActivationRound_final_eq_T_succ p block hlast]
  | some row =>
      simp [boundaryOutputFromFollower, hpending,
        BootstrapObservedFollower.nextActivationRound_final_eq_T_succ p block hlast]

/-- This producer is exactly the accepted `boundaryFollower` adapter at the
completed cursor, including the first-declaration-only initial state/memory. -/
theorem boundaryOutputAtCursor_step (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p))
    (follower : ActualInitializationPhysicalStep.FollowerState p rate block)
    (hcomplete : followerAtCursor p rate block
      (BootstrapObservedFollower.blockLength p block) follower) :
    ActualInitializationPhysicalStep.boundaryFollower rate block follower =
      .ok (boundaryOutputAtCursor p rate block follower hcomplete) := by
  cases follower with
  | bootstrap state =>
      have hcursor : state.processed.val = BootstrapObservedFollower.blockLength p block := by
        simpa [followerAtCursor] using hcomplete
      cases hpending : BootstrapObservedFollower.pendingDeclaration state.blockCase with
      | none =>
          rw [ActualInitializationPhysicalStep.boundaryFollower_continue
            rate block state hcursor hpending]
          simp [boundaryOutputAtCursor, boundaryOutputFromFollower, hpending]
      | some row =>
          rw [ActualInitializationPhysicalStep.boundaryFollower_first_declaration
            rate block state hcursor row hpending]
          simp [boundaryOutputAtCursor, boundaryOutputFromFollower, hpending]
  | declared row activation configuration => rfl

/-- Install only the accepted boundary output. First declaration alone creates
the original ordinary initial state and proposal memory. -/
def followerCarryOfBoundaryOutput {p : Parameters} (rate : RateInput p)
    (output : ActualInitializationPhysicalStep.BoundaryFollowerOutput p rate) :
      FollowerCarry p rate :=
  match output with
  | .continueBootstrap numerators lowerBound _ => .bootstrap numerators lowerBound
  | .firstDeclaration row activation state memory =>
      .declared row activation (.ordinary state memory)
  | .preserveDeclared row activation configuration => .declared row activation configuration

/-- The carried state obtained by applying the accepted block boundary to an
actual post-observation follower. -/
def followerCarryAtBlockBoundary (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p))
    (follower : ActualInitializationPhysicalStep.FollowerState p rate block) : FollowerCarry p rate :=
  followerCarryOfBoundaryOutput rate (boundaryOutputFromFollower p rate block follower)

/-- The carried boundary state is exactly the conversion of the successful
accepted boundary output. -/
theorem followerCarryAtBlockBoundary_eq_output (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p))
    (follower : ActualInitializationPhysicalStep.FollowerState p rate block)
    (hcomplete : followerAtCursor p rate block
      (BootstrapObservedFollower.blockLength p block) follower) :
    followerCarryAtBlockBoundary p rate block follower =
      followerCarryOfBoundaryOutput rate
        (boundaryOutputAtCursor p rate block follower hcomplete) := rfl

/-- The three honest outcomes after a complete clipped block: continue from
the actual carried boundary state, return the exact first launch handoff, or
return a full no-crossing horizon-exhaustion handoff. -/
structure CoordinatorLearnerZeroSeed (p : Parameters) where
  baseScores : Fin p.K → ℕ
  baseScores_eq : baseScores = Bandits.Support.FirstAssignmentLaunch.Input.baseScores p
  queues : Fin p.K → ℕ
  queues_eq : queues = Bandits.Support.FirstAssignmentLaunch.Input.initialQueues p

/-- Both prescribed learner arrays in this launch seed are identically zero. -/
theorem CoordinatorLearnerZeroSeed.baseScores_zero {p : Parameters}
    (seed : CoordinatorLearnerZeroSeed p) (i : Fin p.K) : seed.baseScores i = 0 := by
  simp [seed.baseScores_eq, Bandits.Support.FirstAssignmentLaunch.Input.baseScores]

theorem CoordinatorLearnerZeroSeed.queues_zero {p : Parameters}
    (seed : CoordinatorLearnerZeroSeed p) (i : Fin p.K) : seed.queues i = 0 := by
  simp [seed.queues_eq, Bandits.Support.FirstAssignmentLaunch.Input.initialQueues]

inductive BoundaryDisposition (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p)) where
  | continueNext (next : Fin (n_boot p)) (carry : BlockCarry p rate next)
  | launched (launch : BootstrapCoordinatorLocalRound.LaunchedBlock p)
      (learnerSeed : CoordinatorLearnerZeroSeed p)
  | exhausted (live : BootstrapCoordinatorLocalRound.PrelaunchBlock p)

/-- Combined coordinator/follower handoff after the final own observation.
The source is retained literally, and the selected row/target are checked
against its original shared index and target scalar. -/
structure CombinedBoundaryHandoff (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p))
    (source : BootstrapPrivateRoundStreams.SourceInput p) where
  originalSource : BootstrapPrivateRoundStreams.SourceInput p
  followers : Fin (p.m - 1) → ActualInitializationPhysicalStep.BoundaryFollowerOutput p rate
  selectedRow : CompletePublicTable.CompleteRow p
  selectedRow_eq : selectedRow = source.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p source)
  selectedTarget : Fin p.K
  selectedTarget_eq : selectedTarget =
    BootstrapPhysicalInput.targetArmMap p block source.2
  disposition : BoundaryDisposition p rate block

/-- Simultaneous actual boundary outputs for the final post-observation
follower states. -/
noncomputable def blockBoundaryFollowers {C_star C_h : ℝ} (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p)) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (folded : BlockFoldOutput p rate block source rewards C_star C_h 0) :
      Fin (p.m - 1) → ActualInitializationPhysicalStep.BoundaryFollowerOutput p rate :=
  fun i => boundaryOutputAtCursor p rate block (folded.followers i)
    (blockFold_follower_complete folded i)

/-- Every boundary coordinate is the successful accepted `boundaryFollowers`
entry derived from the real complete fold. -/
theorem blockBoundaryFollowers_step {C_star C_h : ℝ} (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p)) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (folded : BlockFoldOutput p rate block source rewards C_star C_h 0)
    (i : Fin (p.m - 1)) :
    ActualInitializationPhysicalStep.boundaryFollowers rate block folded.followers i =
      .ok (blockBoundaryFollowers p rate block source rewards folded i) := by
  exact boundaryOutputAtCursor_step p rate block (folded.followers i)
    (blockFold_follower_complete folded i)

/-- On the clipped last block, an accepted launch crossing is recorded at the
source's terminal launch round `T + 1`, after the final physical round `T`. -/
theorem launchedAtFinalBlock_sourceRound (p : Parameters)
    (launch : BootstrapCoordinatorLocalRound.LaunchedBlock p)
    (hlast : launch.data.block.val + 1 = n_boot p) :
    launch.monitor.launchPosition + 1 = p.T + 1 := by
  have hindex : BootstrapDimensions.roundBlockIndex p launch.triggerRound =
      launch.data.block := by
    apply Fin.ext
    exact ((BootstrapDimensions.mem_calendarBlock_iff_quotient p launch.data.block
      launch.triggerRound).1 launch.triggerInBlock).symm
  have hend := launch.triggerAtBlockEnd
  unfold BootstrapLaunchMonitor.calendarBlockEnd at hend
  rw [hindex] at hend
  have hterminal : BootstrapDimensions.manuscriptRound p launch.triggerRound = p.T := by
    calc
      BootstrapDimensions.manuscriptRound p launch.triggerRound =
          min p.T ((launch.data.block.val + 1) * B_boot p) := by
            simpa using hend
      _ = BootstrapObservedFollower.blockStop p launch.data.block := rfl
      _ = p.T := BootstrapObservedFollower.finalBlock_endpoint_eq_T p launch.data.block hlast
  exact BootstrapCoordinatorLocalRound.launched_at_horizon_is_terminal p launch hterminal

/-- Consume the complete clipped block boundary. A launch is returned only
after all follower adapters have run; otherwise the exact carried continuation
advances to the original successor block or terminates honestly at the horizon.
No action at `T+1` is constructed. -/
noncomputable def combinedBoundaryHandoff (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p)) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (folded : BlockFoldOutput p rate block source rewards C_star C_h 0) :
      CombinedBoundaryHandoff p rate block source := by
  classical
  have haligned := folded.invariant.1
  change (continuationData p folded.phase).block = block ∧
    (continuationData p folded.phase).ids = source.1.1 ∧
    (continuationData p folded.phase).row =
      source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) ∧
    (continuationData p folded.phase).target =
      BootstrapPhysicalInput.targetArmMap p block source.2 ∧
    (continuationData p folded.phase).C_star = C_star ∧
    (continuationData p folded.phase).C_h = C_h at haligned
  have hrow : (continuationData p folded.phase).row = source.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source) := by
    exact haligned.2.2.1
  have htarget : (continuationData p folded.phase).target =
      BootstrapPhysicalInput.targetArmMap p block source.2 := by
    exact haligned.2.2.2.1
  let outputs := blockBoundaryFollowers p rate block source rewards folded
  let disposition : BoundaryDisposition p rate block := by
    cases hphase : folded.phase with
    | launched launch =>
        exact .launched launch ⟨Bandits.Support.FirstAssignmentLaunch.Input.baseScores p, rfl,
          Bandits.Support.FirstAssignmentLaunch.Input.initialQueues p, rfl⟩
    | prelaunch live =>
        by_cases hlast : block.val + 1 = n_boot p
        · exact .exhausted live
        · have hnext : block.val + 1 < n_boot p := by omega
          let next := successorBlock p block hnext
          let carry : BlockCarry p rate next := {
            coordinator := live.data.coordinator
            monitor := live.monitor
            C_star := C_star
            C_h := C_h
            followers := fun i => followerCarryAtBlockBoundary p rate block
              (folded.followers i)
            activation_ready := by
              intro i
              cases hf : folded.followers i with
              | bootstrap state =>
                  cases hpending : BootstrapObservedFollower.pendingDeclaration state.blockCase with
                  | none =>
                      simp [followerCarryAtBlockBoundary, followerCarryOfBoundaryOutput,
                        boundaryOutputFromFollower, hpending]
                  | some row =>
                      simpa [followerCarryAtBlockBoundary, followerCarryOfBoundaryOutput,
                        boundaryOutputFromFollower, hf, hpending] using
                        nextActivation_le_successorStart p block hnext
              | declared row activation configuration =>
                  have hactivation : activation.val ≤
                      BootstrapObservedFollower.blockStart p block +
                        BootstrapObservedFollower.blockLength p block + 1 := by
                    simpa [followerAtCursor, hf, folded.consumed_eq_blockLength] using
                      folded.invariant.2.2.1 i
                  have hstop : activation.val ≤ BootstrapObservedFollower.blockStop p block + 1 := by
                    rw [← blockStart_add_length_eq_stop]
                    exact hactivation
                  rw [stop_eq_successorStart p block hnext] at hstop
                  simpa [followerCarryAtBlockBoundary, followerCarryOfBoundaryOutput,
                    boundaryOutputFromFollower, hf] using hstop }
          exact .continueNext next carry
  refine ⟨source, outputs, (continuationData p folded.phase).row, hrow,
    (continuationData p folded.phase).target, htarget, disposition⟩

end Bandits.Support.ActualInitializationRun

end
