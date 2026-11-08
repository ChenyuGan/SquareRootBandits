/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.BootstrapCoordinatorLocalRound
public import Bandits.Support.BootstrapObservedFollower
public import Bandits.Support.BootstrapPrivateRoundStreams
public import Bandits.Support.BootstrapPhysicalInput
public import Bandits.Support.CompletePublicTable
public import Bandits.Support.DeclaredFollowerLocalRound
public import Bandits.Support.FiniteBanditModel
public import Bandits.Support.PrivateSourceStreams
public import Bandits.Support.ReferencePrelaunchFollower
public import Bandits.Support.ActiveFollowerLifecycle
public import Bandits.Support.ActiveRoundActions
public import Bandits.Support.ActiveFollowerDownAcceptance
public import Bandits.Support.BootstrapAllCandidateController
public import Bandits.Support.BootstrapDimensions

import Lean.Elab.Tactic.Omega

/-!
# Actual heterogeneous prelaunch physical round

This module composes the accepted local operations into one actual
prelaunch-round transducer, using the fixed published output, the original
private source coordinates, and the denominator-`D` reward table. Its source
is `sources/zip4/manuscript/07_public_setup.tex:27-113`,
`sources/zip4/manuscript/appendix_b_communication.tex:94-165`,
`sources/zip4/manuscript/appendix_a_local_protocol.tex:1-14`, and
`sources/zip4/manuscript/06_interruptions.tex:1-110`.

The block input keeps each follower's own bootstrap cursor or own declared row,
activation and ordinary/dagger configuration. Preparation completes for the
coordinator and every follower before a joint arm profile is formed. The one
grid-feedback vector is derived from that profile and the fixed rounded reward
table by the accepted collision rule. Each local observation transition then
receives only its own entry. The module does not construct a chronological run,
postlaunch coordinator dispatcher, or global boundary fold.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.BootstrapObservedFollower
open Bandits.Support.BootstrapCoordinatorLocalRound
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.BootstrapPhysicalInput
open Bandits.Support.CompletePublicTable
open Bandits.Support.DeclaredFollowerLocalRound
open Bandits.Support.FiniteBanditModel
open Bandits.Support.PrivateSourceStreams
open Bandits.Support.ReferencePrelaunchFollower
open Bandits.Support.ActiveFollowerLifecycle
open Bandits.Support.ActiveFollowerDownAcceptance
open Bandits.Support.ActiveRoundActions
open Bandits.Support.PublicDiscreteDraws

namespace Bandits.Support.ActualInitializationPhysicalStep

abbrev Parameters := ConstructorDimensions.Parameters

/-- The fixed numerical rounded reward grid retained across this physical
round. -/
abbrev GridRewardTable (p : Parameters) :=
  Fin p.T → Fin p.K → Fin (D p + 1)

/-- One follower's heterogeneous state at an actual bootstrap-block round.
The bootstrap constructor contains that follower's own cursor. A declared
constructor contains that follower's own row label, original activation and
complete carried ordinary/dagger configuration. -/
inductive FollowerState (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p)) where
  | bootstrap (state : BootstrapObservedFollower.StartupState p block)
  | declared (row : Fin (M p)) (activation : ReferencePrelaunchFollower.Activation p)
      (configuration : DeclaredFollowerLocalRound.LocalConfiguration p rate)

/-- Pre-observation preparation for one follower. The bootstrap arm is the
accepted choice made from that follower's own cursor and scalar stream. The
declared constructor retains the complete accepted prepared snapshot. -/
inductive PreparedFollower (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p)) where
  | bootstrap (state : BootstrapObservedFollower.StartupState p block)
      (arm : Fin p.K)
  | declared (rowIndex : Fin (M p))
      (activation : ReferencePrelaunchFollower.Activation p)
      (round : DeclaredFollowerLocalRound.PreparedRound p rate)

/-- The chosen arm in either follower preparation branch. -/
def PreparedFollower.arm {p : Parameters} {rate : RateInput p}
    {block : Fin (n_boot p)} : PreparedFollower p rate block → Fin p.K
  | .bootstrap _ arm => arm
  | .declared _ _ round => round.arm

/-- Per-follower choice-time cursor data. Declared activations must already
have taken effect; a bootstrap cursor must be exactly the next calendar
position in its own current block. -/
def followerAtNextCursor {p : Parameters} {rate : RateInput p}
    {block : Fin (n_boot p)} (time : Fin p.T)
    (follower : FollowerState p rate block) : Prop :=
  match follower with
  | .bootstrap state =>
      time ∈ BootstrapDimensions.calendarBlock p block ∧
      state.processed.val < BootstrapObservedFollower.blockLength p block ∧
      time.val = BootstrapObservedFollower.blockStart p block + state.processed.val
  | .declared _ activation _ => activation.val ≤ time.val + 1

/-- The unique selected row index determined by the original coordinator
scalar in the accepted private input. -/
def selectedRowIndex (p : Parameters)
    (source : BootstrapPrivateRoundStreams.SourceInput p) : Fin (M p) :=
  PrivateSourceStreams.coordinatorIndex p source.2.1.2

/-- The complete deterministic prelaunch typing conditions checked before
any physical arm is produced. These conditions do not assert reachability,
message authenticity, or correctness of a past trace. -/
def ActualInputReady (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p)) (time : Fin p.T)
    (coordinator : BootstrapCoordinatorLocalRound.PrelaunchBlock p)
    (followers : Fin (p.m - 1) → FollowerState p rate block)
    (source : BootstrapPrivateRoundStreams.SourceInput p) : Prop :=
  coordinator.data.block = block ∧
  time ∈ BootstrapDimensions.calendarBlock p block ∧
  coordinator.data.ids = source.1.1 ∧
  coordinator.data.row = source.1.2 (selectedRowIndex p source) ∧
  coordinator.data.target = BootstrapPhysicalInput.targetArmMap p block source.2 ∧
  ∀ i, followerAtNextCursor time (followers i)

/-- Input rejection reasons. A failed next-cursor check is an input rejection;
it cannot manufacture a physical arm. -/
inductive InputFailure (p : Parameters) (block : Fin (n_boot p)) where
  | inputNotReady
  | bootstrapObservationRejected (i : Fin (p.m - 1))
      (failure : BootstrapObservedFollower.RoundFailure p block)

/-- Exact local preparation after the shared current-block and public-input
checks have succeeded. Startup consumes its own original player-round scalar;
declared preparation uses its own row, activation and full carried state. -/
noncomputable def prepareFollowerValid {p : Parameters} (rate : RateInput p)
    (block : Fin (n_boot p)) (time : Fin p.T)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) (follower : FollowerState p rate block)
    (hready : followerAtNextCursor time follower) : PreparedFollower p rate block := by
  classical
  cases follower with
  | bootstrap state =>
      let stream : BootstrapPrivateRoundStreams.PlayerRoundScalarStream p := fun t =>
        BootstrapPhysicalInput.playerRoundScalarAt p source.2
          (PublicDiscreteDraws.followerPlayer p.two_le_m i) t
      exact .bootstrap state
        (BootstrapObservedFollower.localArm p block state source.1.1 time stream)
  | declared row activation configuration =>
      have hactive : activation.val ≤ time.val + 1 := hready
      exact .declared row activation (DeclaredFollowerLocalRound.prepare rate i
        (source.1.2 row) activation time hactive configuration)

/-- An actual prepared round contains the accepted coordinator operation and
every follower's own prepared arm. Its source and numerical reward grid are
retained unchanged for feedback derivation. The readiness field and operation
equations prevent callers from replacing any prepared local snapshot. -/
structure PreparedRound (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p)) where
  time : Fin p.T
  source : BootstrapPrivateRoundStreams.SourceInput p
  rewards : GridRewardTable p
  coordinatorInput : BootstrapCoordinatorLocalRound.PrelaunchBlock p
  followerInputs : Fin (p.m - 1) → FollowerState p rate block
  readiness : ActualInputReady p rate block time coordinatorInput followerInputs source
  coordinator : BootstrapCoordinatorLocalRound.PreparedRound p
  coordinator_eq : coordinator = BootstrapCoordinatorLocalRound.prepare p coordinatorInput
    time (by rw [readiness.1]; exact readiness.2.1)
      (BootstrapPhysicalInput.playerRoundScalarAt p source.2
        (ActiveRoundActions.coordinator p.two_le_m) time)
  followers : Fin (p.m - 1) → PreparedFollower p rate block
  followers_eq : ∀ i, followers i = prepareFollowerValid rate block time source i
    (followerInputs i) (readiness.2.2.2.2.2 i)

/-- A successful follower observation keeps the already prepared arm and
returns precisely its next local state. -/
structure FollowerOutcome (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p)) where
  prepared : PreparedFollower p rate block
  next : FollowerState p rate block

/-- Turn an existing finite reward-grid value into the accepted typed local
observation without changing its numerical value. -/
def observationOfGrid (p : Parameters) (y : Fin (D p + 1)) :
    ReferencePrelaunchFollower.Observation p := by
  have hD : (0 : ℝ) < (D p : ℝ) := by exact_mod_cast D_pos p
  have hy : (y.val : ℝ) ≤ (D p : ℝ) := by
    exact_mod_cast (Nat.le_of_lt_succ y.isLt)
  refine ⟨⟨(y.val : ℝ) / (D p : ℝ), ?_⟩, ⟨y, rfl⟩⟩
  exact ⟨div_nonneg (Nat.cast_nonneg _) (le_of_lt hD), (div_le_one hD).2 hy⟩

/-- The typed observation has exactly the selected grid value. -/
theorem observationOfGrid_value (p : Parameters) (y : Fin (D p + 1)) :
    (observationOfGrid p y).val.val = (y.val : ℝ) / (D p : ℝ) := rfl

/-- The single action profile on the real source player and arm carriers. -/
def actionProfile {p : Parameters} {rate : RateInput p}
    {block : Fin (n_boot p)} (prepared : PreparedRound p rate block) :
    FiniteBanditModel.ActionProfile p.m p.K := fun player =>
  if hp : player = ActiveRoundActions.coordinator p.two_le_m then
    prepared.coordinator.arm
  else
    (prepared.followers
      (ActiveRoundActions.followerIndex p.two_le_m player hp)).arm

/-- The finite-grid collision rule on one jointly prepared profile. -/
def gridFeedback {p : Parameters} {rate : RateInput p}
    {block : Fin (n_boot p)} (prepared : PreparedRound p rate block)
    (player : Fin p.m) : Fin (D p + 1) := by
  classical
  exact if FiniteBanditModel.collisionFreeFor (actionProfile prepared) player then
    prepared.rewards prepared.time (actionProfile prepared player) else 0

/-- The fixed coordinator action equation. -/
theorem actionProfile_coordinator {p : Parameters} {rate : RateInput p}
    {block : Fin (n_boot p)} (prepared : PreparedRound p rate block) :
    actionProfile prepared (ActiveRoundActions.coordinator p.two_le_m) =
      prepared.coordinator.arm := by
  simp [actionProfile]

/-- Each follower's action equation uses that follower's own prepared arm. -/
theorem actionProfile_follower {p : Parameters} {rate : RateInput p}
    {block : Fin (n_boot p)} (prepared : PreparedRound p rate block)
    (i : Fin (p.m - 1)) :
    actionProfile prepared (PublicDiscreteDraws.followerPlayer p.two_le_m i) =
      (prepared.followers i).arm := by
  unfold actionProfile
  rw [dite_eq_right (ActiveRoundActions.followerPlayer_ne_coordinator p.two_le_m i)]
  rw [ActiveRoundActions.followerIndex_followerPlayer p.two_le_m i
    (ActiveRoundActions.followerPlayer_ne_coordinator p.two_le_m i)]

/-- A collision in the prepared physical vector gives exactly zero grid
feedback. -/
theorem gridFeedback_eq_zero_of_collision {p : Parameters} {rate : RateInput p}
    {block : Fin (n_boot p)} (prepared : PreparedRound p rate block)
    (player : Fin p.m)
    (hcollision : ¬ FiniteBanditModel.collisionFreeFor
      (actionProfile prepared) player) :
    gridFeedback prepared player = 0 := by
  simp [gridFeedback, hcollision]

/-- A collision-free player receives the fixed rounded reward on its prepared
arm. -/
theorem gridFeedback_eq_reward_of_collision_free {p : Parameters}
    {rate : RateInput p} {block : Fin (n_boot p)}
    (prepared : PreparedRound p rate block) (player : Fin p.m)
    (hfree : FiniteBanditModel.collisionFreeFor (actionProfile prepared) player) :
    gridFeedback prepared player =
      prepared.rewards prepared.time (actionProfile prepared player) := by
  simp [gridFeedback, hfree]

/-- The physical vectors are derived solely from the prepared arm profile and
the one fixed rounded table. -/
def physicalActions {p : Parameters} {rate : RateInput p}
    {block : Fin (n_boot p)} (prepared : PreparedRound p rate block) :
    FiniteBanditModel.ActionProfile p.m p.K := actionProfile prepared

def physicalFeedback {p : Parameters} {rate : RateInput p}
    {block : Fin (n_boot p)} (prepared : PreparedRound p rate block) :
    Fin p.m → Fin (D p + 1) := gridFeedback prepared

/-- Exact accepted bootstrap arm equation: this follower's activity, held arm
and ID are carried by its state and its original scalar is read at this round. -/
theorem prepareFollowerValid_bootstrap_arm {p : Parameters}
    (rate : RateInput p) (block : Fin (n_boot p)) (time : Fin p.T)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) (state : BootstrapObservedFollower.StartupState p block)
    (hready : followerAtNextCursor time (.bootstrap state)) :
    (prepareFollowerValid rate block time source i (.bootstrap state) hready).arm =
      BootstrapObservedFollower.localArm p block state source.1.1 time
        (fun t => BootstrapPhysicalInput.playerRoundScalarAt p source.2
          (PublicDiscreteDraws.followerPlayer p.two_le_m i) t) := rfl

/-- Active startup uses its own held/ID state and its own source scalar. -/
theorem prepareFollowerValid_bootstrap_active {p : Parameters}
    (rate : RateInput p) (block : Fin (n_boot p)) (time : Fin p.T)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) (state : BootstrapObservedFollower.StartupState p block)
    (held : Fin p.K) (privateID : Fin (A_id p)) (gain : ℕ)
    (registers : BootstrapAllCandidateController.Registers p)
    (hcase : state.blockCase = .active held privateID gain registers)
    (hready : followerAtNextCursor time (.bootstrap state)) :
    (prepareFollowerValid rate block time source i (.bootstrap state) hready).arm =
      if source.1.1 privateID time then
        (BootstrapPrivateRoundStreams.forbiddenArmScalarDraw p held
          (BootstrapPhysicalInput.playerRoundScalarAt p source.2
            (PublicDiscreteDraws.followerPlayer p.two_le_m i) time)).val
      else held := by
  rw [prepareFollowerValid_bootstrap_arm]
  exact BootstrapObservedFollower.localArm_active p block state source.1.1 time
    (fun t => BootstrapPhysicalInput.playerRoundScalarAt p source.2
      (PublicDiscreteDraws.followerPlayer p.two_le_m i) t)
    held privateID gain registers hcase

/-- Inactive startup uses its own original full-arm scalar. -/
theorem prepareFollowerValid_bootstrap_inactive {p : Parameters}
    (rate : RateInput p) (block : Fin (n_boot p)) (time : Fin p.T)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) (state : BootstrapObservedFollower.StartupState p block)
    (hcase : state.blockCase = .inactive)
    (hready : followerAtNextCursor time (.bootstrap state)) :
    (prepareFollowerValid rate block time source i (.bootstrap state) hready).arm =
      BootstrapPrivateRoundStreams.fullArmScalarDraw p
        (BootstrapPhysicalInput.playerRoundScalarAt p source.2
          (PublicDiscreteDraws.followerPlayer p.two_le_m i) time) := by
  rw [prepareFollowerValid_bootstrap_arm]
  exact BootstrapObservedFollower.localArm_inactive p block state source.1.1 time
    (fun t => BootstrapPhysicalInput.playerRoundScalarAt p source.2
      (PublicDiscreteDraws.followerPlayer p.two_le_m i) t) hcase

/-- Activated ordinary preparation uses exactly the accepted declared-row
operation, including its own activation and carried local memory. -/
theorem prepareFollowerValid_declared_arm {p : Parameters}
    (rate : RateInput p) (block : Fin (n_boot p)) (time : Fin p.T)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) (row : Fin (M p))
    (activation : ReferencePrelaunchFollower.Activation p)
    (configuration : DeclaredFollowerLocalRound.LocalConfiguration p rate)
    (hready : followerAtNextCursor time (.declared row activation configuration)) :
    (prepareFollowerValid rate block time source i
      (.declared row activation configuration) hready).arm =
      (DeclaredFollowerLocalRound.prepare rate i (source.1.2 row) activation time
        hready configuration).arm := rfl

/-- A daggered declared follower uses the corrected local fallback arm. -/
theorem prepareFollowerValid_dagger_arm {p : Parameters}
    (rate : RateInput p) (block : Fin (n_boot p)) (time : Fin p.T)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) (row : Fin (M p))
    (activation : ReferencePrelaunchFollower.Activation p)
    (hready : followerAtNextCursor time (.declared row activation .dagger)) :
    (prepareFollowerValid rate block time source i
      (.declared row activation .dagger) hready).arm =
      DeclaredFollowerLocalRound.fallbackArm p i := by
  have hactive : activation.val ≤ time.val + 1 := hready
  exact (DeclaredFollowerLocalRound.prepare_dagger rate i (source.1.2 row)
    activation time hactive).1

/-- The complete preparation operation checks all coordinator and follower
typing data before constructing any physical arm profile. -/
noncomputable def prepare {p : Parameters} (rate : RateInput p)
    (block : Fin (n_boot p)) (time : Fin p.T)
    (coordinator : BootstrapCoordinatorLocalRound.PrelaunchBlock p)
    (followers : Fin (p.m - 1) → FollowerState p rate block)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : GridRewardTable p) :
    Except (InputFailure p block) (PreparedRound p rate block) := by
  classical
  if hready : ActualInputReady p rate block time coordinator followers source then
    have htime : time ∈ BootstrapDimensions.calendarBlock p coordinator.data.block := by
      rw [hready.1]
      exact hready.2.1
    let coord := BootstrapCoordinatorLocalRound.prepare p coordinator time htime
      (BootstrapPhysicalInput.playerRoundScalarAt p source.2
        (ActiveRoundActions.coordinator p.two_le_m) time)
    exact .ok
      { time := time
        source := source
        rewards := rewards
        coordinatorInput := coordinator
        followerInputs := followers
        readiness := hready
        coordinator := coord
        coordinator_eq := rfl
        followers := fun i => prepareFollowerValid rate block time source i
          (followers i) (hready.2.2.2.2.2 i)
        followers_eq := fun _ => rfl }
  else exact .error .inputNotReady

/-- Preparation succeeds exactly when the selected coordinator block, time,
shared IDs, original-`J` row, original target draw, and every local next cursor
match their explicit source typing data. -/
theorem prepare_eq_ok_iff_ready {p : Parameters} (rate : RateInput p)
    (block : Fin (n_boot p)) (time : Fin p.T)
    (coordinator : BootstrapCoordinatorLocalRound.PrelaunchBlock p)
    (followers : Fin (p.m - 1) → FollowerState p rate block)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : GridRewardTable p) :
    (∃ output, prepare rate block time coordinator followers source rewards =
      .ok output) ↔ ActualInputReady p rate block time coordinator followers source := by
  classical
  by_cases hready : ActualInputReady p rate block time coordinator followers source
  · simp [prepare, hready]
  · simp [prepare, hready]

/-- The coordinator arm equation records the original row `J` and that
coordinator's own original player-round scalar. -/
theorem prepared_coordinator_arm_eq_choice {p : Parameters}
    {rate : RateInput p} {block : Fin (n_boot p)}
    (prepared : PreparedRound p rate block) :
    prepared.coordinator.arm =
      BootstrapCoordinatorLocalRound.coordinatorArmChoice p
        (prepared.source.1.2 (selectedRowIndex p prepared.source))
        (BootstrapPhysicalInput.targetArmMap p block prepared.source.2)
        prepared.coordinatorInput.data.coordinator prepared.time
        (BootstrapPhysicalInput.playerRoundScalarAt p prepared.source.2
          (ActiveRoundActions.coordinator p.two_le_m) prepared.time) := by
  calc
    prepared.coordinator.arm =
        (BootstrapCoordinatorLocalRound.prepare p prepared.coordinatorInput
          prepared.time
          (by rw [prepared.readiness.1]; exact prepared.readiness.2.1)
          (BootstrapPhysicalInput.playerRoundScalarAt p prepared.source.2
            (ActiveRoundActions.coordinator p.two_le_m) prepared.time)).arm :=
      congrArg BootstrapCoordinatorLocalRound.PreparedRound.arm prepared.coordinator_eq
    _ = BootstrapCoordinatorLocalRound.coordinatorArmChoice p
        prepared.coordinatorInput.data.row prepared.coordinatorInput.data.target
        prepared.coordinatorInput.data.coordinator prepared.time
        (BootstrapPhysicalInput.playerRoundScalarAt p prepared.source.2
          (ActiveRoundActions.coordinator p.two_le_m) prepared.time) :=
      BootstrapCoordinatorLocalRound.prepare_arm_eq_choice p prepared.coordinatorInput
        prepared.time
        (by rw [prepared.readiness.1]; exact prepared.readiness.2.1)
        (BootstrapPhysicalInput.playerRoundScalarAt p prepared.source.2
          (ActiveRoundActions.coordinator p.two_le_m) prepared.time)
    _ = BootstrapCoordinatorLocalRound.coordinatorArmChoice p
        (prepared.source.1.2 (selectedRowIndex p prepared.source))
        (BootstrapPhysicalInput.targetArmMap p block prepared.source.2)
        prepared.coordinatorInput.data.coordinator prepared.time
        (BootstrapPhysicalInput.playerRoundScalarAt p prepared.source.2
          (ActiveRoundActions.coordinator p.two_le_m) prepared.time) := by
      rw [prepared.readiness.2.2.2.1, prepared.readiness.2.2.2.2.1]

/-- One follower's actual observation operation. Bootstrap candidate tests
read the full accepted candidate-row family; declared local processing sees
only this follower's own physically derived feedback. -/
def observeFollower {p : Parameters} (rate : RateInput p)
    (block : Fin (n_boot p)) (time : Fin p.T)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) (prepared : PreparedFollower p rate block)
    (ownFeedback : Fin (D p + 1)) :
    Except (InputFailure p block) (FollowerOutcome p rate block) := by
  classical
  cases prepared with
  | bootstrap state arm =>
      match BootstrapObservedFollower.observe p block state source.1.1 source.1.2
          time (observationOfGrid p ownFeedback) with
      | .rejected error => exact .error (.bootstrapObservationRejected i error)
      | .accepted next => exact .ok ⟨.bootstrap state arm, .bootstrap next⟩
  | declared rowIndex activation round =>
      let observed := DeclaredFollowerLocalRound.observe round
        (observationOfGrid p ownFeedback)
      exact .ok ⟨.declared rowIndex activation round,
        .declared rowIndex activation observed.configuration⟩

/-- A declaration saved by a bootstrap observation remains a startup state
for every remaining round in that block. Thus its bootstrap arm and full-block
gain continue until the actual boundary adapter is called. -/
theorem observeFollower_bootstrap_next_is_startup {p : Parameters}
    (rate : RateInput p) (block : Fin (n_boot p)) (time : Fin p.T)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) (state next : BootstrapObservedFollower.StartupState p block)
    (arm : Fin p.K) (ownFeedback : Fin (D p + 1))
    (hobserve : BootstrapObservedFollower.observe p block state source.1.1
      source.1.2 time (observationOfGrid p ownFeedback) = .accepted next) :
    observeFollower rate block time source i (.bootstrap state arm) ownFeedback =
      .ok ⟨.bootstrap state arm, .bootstrap next⟩ := by
  simp [observeFollower, hobserve]

/-- Activated observation continuation is exactly the accepted declared-row
operation on this follower's own physically derived observation. -/
theorem observeFollower_declared_eq {p : Parameters}
    (rate : RateInput p) (block : Fin (n_boot p)) (time : Fin p.T)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1))
    (rowIndex : Fin (M p))
    (activation : ReferencePrelaunchFollower.Activation p)
    (round : DeclaredFollowerLocalRound.PreparedRound p rate)
    (ownFeedback : Fin (D p + 1)) :
    observeFollower rate block time source i (.declared rowIndex activation round) ownFeedback =
      .ok ⟨.declared rowIndex activation round,
        .declared rowIndex activation
          (DeclaredFollowerLocalRound.observe round
            (observationOfGrid p ownFeedback)).configuration⟩ := rfl


/-- A daggered declared follower stays local and absorbing after its own
feedback entry. -/
theorem observeFollower_declared_dagger_absorbing {p : Parameters}
    (rate : RateInput p) (block : Fin (n_boot p)) (time : Fin p.T)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1))
    (rowIndex : Fin (M p))
    (activation : ReferencePrelaunchFollower.Activation p)
    (round : DeclaredFollowerLocalRound.PreparedRound p rate)
    (hdagger : round.configuration = .dagger)
    (ownFeedback : Fin (D p + 1)) :
    (observeFollower rate block time source i
        (.declared rowIndex activation round) ownFeedback).map
        FollowerOutcome.next =
      .ok (.declared rowIndex activation .dagger) := by
  have hobs := DeclaredFollowerLocalRound.observe_dagger_absorbing round
    (observationOfGrid p ownFeedback) hdagger
  unfold observeFollower
  change Except.ok (ε := InputFailure p block) (FollowerState.declared rowIndex activation
    (DeclaredFollowerLocalRound.observe round
      (observationOfGrid p ownFeedback)).configuration) =
    Except.ok (ε := InputFailure p block)
      (FollowerState.declared rowIndex activation .dagger)
  rw [hobs]

/-- Every successful local observation retains the prepared arm verbatim. -/
theorem observeFollower_preserves_prepared_arm {p : Parameters}
    (rate : RateInput p) (block : Fin (n_boot p)) (time : Fin p.T)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) (prepared : PreparedFollower p rate block)
    (ownFeedback : Fin (D p + 1)) (outcome : FollowerOutcome p rate block)
    (h : observeFollower rate block time source i prepared ownFeedback = .ok outcome) :
    outcome.prepared.arm = prepared.arm := by
  cases prepared with
  | bootstrap state arm =>
      cases hobs : BootstrapObservedFollower.observe p block state source.1.1
          source.1.2 time (observationOfGrid p ownFeedback) with
      | rejected error => simp [observeFollower, hobs] at h
      | accepted next =>
          simp only [observeFollower, hobs, Except.ok.injEq] at h
          cases h
          rfl
  | declared rowIndex activation round =>
      simp only [observeFollower, Except.ok.injEq] at h
      cases h
      rfl

/-- A prepared follower always has its exact accepted continuation. Bootstrap
acceptance follows from that follower's next-cursor proof; the declared
operation is total on its complete carried local configuration. -/
theorem observeFollower_success_of_state {p : Parameters} (rate : RateInput p)
    (block : Fin (n_boot p)) (time : Fin p.T)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) (follower : FollowerState p rate block)
    (hready : followerAtNextCursor time follower)
    (ownFeedback : Fin (D p + 1)) :
    ∃ outcome, observeFollower rate block time source i
      (prepareFollowerValid rate block time source i follower hready) ownFeedback =
        .ok outcome := by
  classical
  cases follower with
  | bootstrap state =>
      have hcursor : followerAtNextCursor (p := p) (rate := rate) time
          (.bootstrap state) := hready
      have hobs := BootstrapObservedFollower.observe_accepted_processed p block state
        source.1.1 source.1.2 time (observationOfGrid p ownFeedback)
        hcursor.1 hcursor.2.1 hcursor.2.2
      let arm := BootstrapObservedFollower.localArm p block state source.1.1 time
        (fun t => BootstrapPhysicalInput.playerRoundScalarAt p source.2
          (PublicDiscreteDraws.followerPlayer p.two_le_m i) t)
      let next := BootstrapObservedFollower.observeOne p block state source.1.1
        source.1.2 time (observationOfGrid p ownFeedback)
        hcursor.1 hcursor.2.1 hcursor.2.2
      refine ⟨⟨.bootstrap state arm, .bootstrap next⟩, ?_⟩
      simp [prepareFollowerValid, observeFollower, hobs, arm, next]
  | declared row activation configuration =>
      let round := DeclaredFollowerLocalRound.prepare rate i (source.1.2 row)
        activation time hready configuration
      refine ⟨⟨.declared row activation round,
        .declared row activation
          (DeclaredFollowerLocalRound.observe round (observationOfGrid p ownFeedback)).configuration⟩,
        ?_⟩
      simp [prepareFollowerValid, observeFollower, round,
        DeclaredFollowerLocalRound.prepare]

/-- Every follower in a prepared physical round has its successful local
continuation, using only its own entry of the derived feedback vector. -/
theorem observeFollower_success {p : Parameters} {rate : RateInput p}
    {block : Fin (n_boot p)} (prepared : PreparedRound p rate block)
    (i : Fin (p.m - 1)) :
    ∃ outcome, observeFollower rate block prepared.time prepared.source i
      (prepared.followers i)
      (physicalFeedback prepared
        (PublicDiscreteDraws.followerPlayer p.two_le_m i)) = .ok outcome := by
  rw [prepared.followers_eq i]
  exact observeFollower_success_of_state rate block prepared.time prepared.source i
    (prepared.followerInputs i) (prepared.readiness.2.2.2.2.2 i)
    (physicalFeedback prepared (PublicDiscreteDraws.followerPlayer p.two_le_m i))

/-- Apply each local observation to that follower using only its entry of the
already derived simultaneous feedback vector. -/
noncomputable def observeFollowers {p : Parameters} {rate : RateInput p}
    {block : Fin (n_boot p)} (prepared : PreparedRound p rate block) :
    {outcomes : Fin (p.m - 1) → FollowerOutcome p rate block //
      ∀ i, observeFollower rate block prepared.time prepared.source i
        (prepared.followers i)
        (physicalFeedback prepared (PublicDiscreteDraws.followerPlayer p.two_le_m i)) =
          .ok (outcomes i)} := by
  classical
  refine ⟨fun i => Classical.choose (observeFollower_success prepared i), ?_⟩
  intro i
  exact Classical.choose_spec (observeFollower_success prepared i)

/-- Complete result of one actual prelaunch physical round. Its follower
continuations carry a proof that they were computed by the accepted local
operations from their own entries of the derived feedback vector. -/
structure RoundResult (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p)) where
  prepared : PreparedRound p rate block
  followers : Fin (p.m - 1) → FollowerOutcome p rate block
  followerTransition : ∀ i, observeFollower rate block prepared.time prepared.source i
    (prepared.followers i)
    (physicalFeedback prepared (PublicDiscreteDraws.followerPlayer p.two_le_m i)) =
      .ok (followers i)

/-- The physical simultaneous arm vector of a successful round result. -/
def RoundResult.actions {p : Parameters} {rate : RateInput p}
    {block : Fin (n_boot p)} (result : RoundResult p rate block) :
    FiniteBanditModel.ActionProfile p.m p.K := actionProfile result.prepared

/-- The physical finite-grid feedback vector of a successful round result. -/
def RoundResult.feedback {p : Parameters} {rate : RateInput p}
    {block : Fin (n_boot p)} (result : RoundResult p rate block) :
    Fin p.m → Fin (D p + 1) := physicalFeedback result.prepared

/-- The coordinator's accepted local observation continuation. -/
def RoundResult.coordinator {p : Parameters} {rate : RateInput p}
    {block : Fin (n_boot p)} (result : RoundResult p rate block) :
    BootstrapCoordinatorLocalRound.ObservationResult p :=
  BootstrapCoordinatorLocalRound.observe result.prepared.coordinator
    (result.feedback (ActiveRoundActions.coordinator p.two_le_m))

/-- Observe one prepared physical round only after its simultaneous action and
feedback vectors have been computed. -/
def observePrepared {p : Parameters}
    {rate : RateInput p} {block : Fin (n_boot p)}
    (prepared : PreparedRound p rate block) :
    Except (InputFailure p block) (RoundResult p rate block) := by
  let nextFollowers := observeFollowers prepared
  exact .ok ⟨prepared, nextFollowers.val, nextFollowers.property⟩

/-- The checked actual one-round transducer: validate and prepare every local
arm, form one physical vector, derive finite-grid feedback, then observe. -/
noncomputable def step {p : Parameters} (rate : RateInput p)
    (block : Fin (n_boot p)) (time : Fin p.T)
    (coordinator : BootstrapCoordinatorLocalRound.PrelaunchBlock p)
    (followers : Fin (p.m - 1) → FollowerState p rate block)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : GridRewardTable p) :
    Except (InputFailure p block) (RoundResult p rate block) := by
  match prepare rate block time coordinator followers source rewards with
  | .error error => exact .error error
  | .ok prepared => exact observePrepared prepared

/-- The actual physical step succeeds exactly for the explicitly typed current
block, source selection, coordinator, and every follower's own next cursor. -/
theorem step_succeeds_iff_ready {p : Parameters} (rate : RateInput p)
    (block : Fin (n_boot p)) (time : Fin p.T)
    (coordinator : BootstrapCoordinatorLocalRound.PrelaunchBlock p)
    (followers : Fin (p.m - 1) → FollowerState p rate block)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : GridRewardTable p) :
    (∃ result, step rate block time coordinator followers source rewards = .ok result) ↔
      ActualInputReady p rate block time coordinator followers source := by
  constructor
  · rintro ⟨result, hresult⟩
    unfold step at hresult
    cases hprepare : prepare rate block time coordinator followers source rewards with
    | error error => simp [hprepare] at hresult
    | ok prepared =>
        exact (prepare_eq_ok_iff_ready rate block time coordinator followers source
          rewards).mp ⟨prepared, hprepare⟩
  · intro hready
    rcases (prepare_eq_ok_iff_ready rate block time coordinator followers source
      rewards).mpr hready with ⟨prepared, hprepare⟩
    let observedMap := observeFollowers prepared
    refine ⟨⟨prepared, observedMap.val, observedMap.property⟩, ?_⟩
    simp [step, hprepare, observePrepared, observedMap]

/-- Feedback is exactly the accepted finite-grid collision rule on the
prepared action profile and fixed rounded table. -/
theorem roundResult_feedback_eq_grid {p : Parameters} {rate : RateInput p}
    {block : Fin (n_boot p)} (result : RoundResult p rate block)
    (player : Fin p.m) :
    result.feedback player = gridFeedback result.prepared player := rfl

/-- The coordinator's prepared arm is unchanged by its observation
processing. -/
theorem roundResult_coordinator_arm_preserved {p : Parameters}
    {rate : RateInput p} {block : Fin (n_boot p)}
    (result : RoundResult p rate block) :
    result.coordinator.arm = result.prepared.coordinator.arm := by
  exact BootstrapCoordinatorLocalRound.observe_preserves_prepared_arm
    result.prepared.coordinator
    (result.feedback (ActiveRoundActions.coordinator p.two_le_m))

/-- Every follower's prepared arm is unchanged by its observation processing. -/
theorem roundResult_follower_arm_preserved {p : Parameters}
    {rate : RateInput p} {block : Fin (n_boot p)}
    (result : RoundResult p rate block) (i : Fin (p.m - 1)) :
    (result.followers i).prepared.arm = (result.prepared.followers i).arm := by
  exact observeFollower_preserves_prepared_arm rate block result.prepared.time
    result.prepared.source i (result.prepared.followers i)
    (result.feedback (PublicDiscreteDraws.followerPlayer p.two_le_m i))
    (result.followers i) (result.followerTransition i)

/-- Each physical player receives exactly its own entry of the derived
simultaneous feedback vector. -/
theorem roundResult_coordinator_feedback {p : Parameters} {rate : RateInput p}
    {block : Fin (n_boot p)} (result : RoundResult p rate block) :
    result.feedback (ActiveRoundActions.coordinator p.two_le_m) =
      gridFeedback result.prepared (ActiveRoundActions.coordinator p.two_le_m) := rfl

theorem roundResult_follower_feedback {p : Parameters} {rate : RateInput p}
    {block : Fin (n_boot p)} (result : RoundResult p rate block)
    (i : Fin (p.m - 1)) :
    result.feedback (PublicDiscreteDraws.followerPlayer p.two_le_m i) =
      gridFeedback result.prepared (PublicDiscreteDraws.followerPlayer p.two_le_m i) := rfl

/-- Boundary outcomes for one follower. Only first declaration constructs a
new ordinary state. -/
inductive BoundaryFollowerOutput (p : Parameters) (rate : RateInput p) where
  | continueBootstrap (numerators : Fin p.K → ℕ)
      (lowerBound : ∀ a, 1 ≤ BootstrapWeightPotential.weight (b_N p) numerators a)
      (activation : ReferencePrelaunchFollower.Activation p)
  | firstDeclaration (row : Fin (M p))
      (activation : ReferencePrelaunchFollower.Activation p)
      (state : ReferencePrelaunchFollower.State p rate.eta)
      (memory : ActiveFollowerLifecycle.LocalMemory p)
  | preserveDeclared (row : Fin (M p))
      (activation : ReferencePrelaunchFollower.Activation p)
      (configuration : DeclaredFollowerLocalRound.LocalConfiguration p rate)

/-- Adapt the actual accepted bootstrap `finishBlock` result. The declaration
branch alone creates the true empty reference state and empty proposal memory.
-/
def adaptBootstrapFinish {p : Parameters} (rate : RateInput p)
    (block : Fin (n_boot p))
    (finished : Except (BootstrapObservedFollower.FinishFailure p block)
      (BootstrapObservedFollower.BoundaryOutput p block)) :
    Except (BootstrapObservedFollower.FinishFailure p block)
      (BoundaryFollowerOutput p rate) := by
  cases finished with
  | error failure => exact .error failure
  | ok boundary =>
      cases boundary with
      | continueWithWeights numerators lowerBound activation =>
          exact .ok (.continueBootstrap numerators lowerBound activation)
      | declareRow row activation =>
          exact .ok (.firstDeclaration row activation
            (ReferencePrelaunchFollower.initial p rate.eta)
            (ActiveFollowerLifecycle.initialMemory p))

/-- Continuing bootstrap retains exactly the numerators computed by the
accepted full-block update, including gain after a declaration was saved. -/
theorem adaptBootstrapFinish_continue {p : Parameters}
    (rate : RateInput p) (block : Fin (n_boot p))
    (numerators : Fin p.K → ℕ)
    (lowerBound : ∀ a, 1 ≤ BootstrapWeightPotential.weight (b_N p) numerators a)
    (activation : ReferencePrelaunchFollower.Activation p) :
    adaptBootstrapFinish rate block
      (.ok (.continueWithWeights numerators lowerBound activation)) =
        .ok (.continueBootstrap numerators lowerBound activation) := rfl

/-- A declared row from `finishBlock` alone creates the initial ordinary
registers and true empty proposal memory. -/
theorem adaptBootstrapFinish_declare {p : Parameters}
    (rate : RateInput p) (block : Fin (n_boot p))
    (row : Fin (M p)) (activation : ReferencePrelaunchFollower.Activation p) :
    adaptBootstrapFinish rate block (.ok (.declareRow row activation)) =
      .ok (.firstDeclaration row activation
        (ReferencePrelaunchFollower.initial p rate.eta)
        (ActiveFollowerLifecycle.initialMemory p)) := rfl

/-- The actual accepted `finishBlock` declaration adapter. -/
theorem actual_finish_declaration_adapter {p : Parameters}
    (rate : RateInput p) (block : Fin (n_boot p))
    (state : BootstrapObservedFollower.StartupState p block)
    (hcomplete : state.processed.val = BootstrapObservedFollower.blockLength p block)
    (row : Fin (M p))
    (hpending : BootstrapObservedFollower.pendingDeclaration state.blockCase = some row) :
    adaptBootstrapFinish rate block (BootstrapObservedFollower.finishBlock p block state) =
      .ok (.firstDeclaration row (BootstrapObservedFollower.nextActivationRound p block)
        (ReferencePrelaunchFollower.initial p rate.eta)
        (ActiveFollowerLifecycle.initialMemory p)) := by
  rw [BootstrapObservedFollower.finishBlock_declare p block state hcomplete row hpending]
  rfl

/-- The declaration activation coordinate is the exclusive block stop plus
one, so a clipped final block carries terminal activation `T + 1`. -/
theorem actual_finish_declaration_terminal {p : Parameters}
    (rate : RateInput p) (block : Fin (n_boot p))
    (state : BootstrapObservedFollower.StartupState p block)
    (hcomplete : state.processed.val = BootstrapObservedFollower.blockLength p block)
    (row : Fin (M p))
    (hpending : BootstrapObservedFollower.pendingDeclaration state.blockCase = some row)
    (hlast : block.val + 1 = n_boot p) :
    adaptBootstrapFinish rate block (BootstrapObservedFollower.finishBlock p block state) =
      .ok (.firstDeclaration row ⟨p.T + 1, by omega⟩
        (ReferencePrelaunchFollower.initial p rate.eta)
        (ActiveFollowerLifecycle.initialMemory p)) := by
  rw [BootstrapObservedFollower.finishBlock_terminal_activation p block state
    hcomplete row hpending hlast]
  rfl

/-- Boundary handoff for a follower: a bootstrap state uses its accepted
clipped `finishBlock`; an already declared follower preserves its full row,
activation and local configuration. -/
def boundaryFollower {p : Parameters} (rate : RateInput p)
    (block : Fin (n_boot p)) (follower : FollowerState p rate block) :
    Except (BootstrapObservedFollower.FinishFailure p block)
      (BoundaryFollowerOutput p rate) := by
  cases follower with
  | bootstrap state =>
      exact adaptBootstrapFinish rate block
        (BootstrapObservedFollower.finishBlock p block state)
  | declared row activation configuration =>
      exact .ok (.preserveDeclared row activation configuration)

/-- Simultaneous boundary handoffs for all followers. Each coordinate retains
its own accepted bootstrap/declaration outcome; aggregation with the
coordinator continuation belongs to the later chronological boundary fold. -/
def boundaryFollowers {p : Parameters} (rate : RateInput p)
    (block : Fin (n_boot p))
    (followers : Fin (p.m - 1) → FollowerState p rate block) :
    Fin (p.m - 1) →
      Except (BootstrapObservedFollower.FinishFailure p block)
        (BoundaryFollowerOutput p rate) :=
  fun i => boundaryFollower rate block (followers i)

/-- A later declared boundary preserves the entire ordinary or dagger state
and memory, together with its row label and original activation. -/
theorem boundaryFollower_declared {p : Parameters}
    (rate : RateInput p) (block : Fin (n_boot p))
    (row : Fin (M p)) (activation : ReferencePrelaunchFollower.Activation p)
    (configuration : DeclaredFollowerLocalRound.LocalConfiguration p rate) :
    boundaryFollower rate block (.declared row activation configuration) =
      .ok (.preserveDeclared row activation configuration) := rfl

/-- A successful first declaration installs only the specified accepted row
and the empty local initial state; its activation is exactly `blockStop + 1`.
-/
theorem boundaryFollower_first_declaration {p : Parameters}
    (rate : RateInput p) (block : Fin (n_boot p))
    (state : BootstrapObservedFollower.StartupState p block)
    (hcomplete : state.processed.val = BootstrapObservedFollower.blockLength p block)
    (row : Fin (M p))
    (hpending : BootstrapObservedFollower.pendingDeclaration state.blockCase = some row) :
    boundaryFollower rate block (.bootstrap state) =
      .ok (.firstDeclaration row (BootstrapObservedFollower.nextActivationRound p block)
        (ReferencePrelaunchFollower.initial p rate.eta)
        (ActiveFollowerLifecycle.initialMemory p)) :=
  actual_finish_declaration_adapter rate block state hcomplete row hpending

/-- A completed block with no pending declaration carries the updated
bootstrap numerators out unchanged. -/
theorem boundaryFollower_continue {p : Parameters}
    (rate : RateInput p) (block : Fin (n_boot p))
    (state : BootstrapObservedFollower.StartupState p block)
    (hcomplete : state.processed.val = BootstrapObservedFollower.blockLength p block)
    (hnone : BootstrapObservedFollower.pendingDeclaration state.blockCase = none) :
    boundaryFollower rate block (.bootstrap state) =
      .ok (.continueBootstrap (BootstrapObservedFollower.updatedNumerators p block state)
        (BootstrapObservedFollower.updatedNumerators_lower_bound p block state)
        (BootstrapObservedFollower.nextActivationRound p block)) := by
  change adaptBootstrapFinish rate block
    (BootstrapObservedFollower.finishBlock p block state) = _
  rw [BootstrapObservedFollower.finishBlock_continue p block state hcomplete hnone]
  rfl

end Bandits.Support.ActualInitializationPhysicalStep

end
