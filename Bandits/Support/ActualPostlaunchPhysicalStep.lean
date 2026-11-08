/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.OrdinaryCoordinatorPhysicalInterface
public import Bandits.Support.ActualInitializationSourceObservation

/-!
# The actual mixed postlaunch physical step

This module joins the accepted local coordinator operation to the actual
heterogeneous bootstrap/declared follower operation. It uses one original
source, one fixed denominator-`D` reward table, the actual clipped-block
calendar, and each follower's own retained state. It does not define a horizon
fold or a probability law.

Mathematical evidence: `sources/zip4/manuscript/07_public_setup.tex:55-114`,
`sources/zip4/manuscript/06_interruptions.tex:240-296`,
`sources/zip4/manuscript/appendix_a_local_protocol.tex:6-14`, and
`sources/zip4/manuscript/appendix_b_communication.tex:94-131`.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.BootstrapObservedFollower
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.ActiveRoundActions
open Bandits.Support.PublicDiscreteDraws
open Bandits.Support.FiniteBanditModel
open Bandits.Support.ReferencePrelaunchFollower

namespace Bandits.Support.ActualPostlaunchPhysicalStep

abbrev Parameters := ActualInitializationPhysicalStep.Parameters
abbrev RateInput := ActualInitializationSourceObservation.RateInput
abbrev SourceInput (p : Parameters) := BootstrapPrivateRoundStreams.SourceInput p
abbrev GridRewardTable (p : Parameters) := ActualInitializationPhysicalStep.GridRewardTable p

variable {p : Parameters} {rate : RateInput p}

/-- The persistent postlaunch data at one actual block cursor. The coordinator
configuration and decoder bank are their accepted existing carriers. Each
follower retains its own bootstrap startup, or its own declared row,
activation, and full ordinary/dagger configuration. -/
structure PostlaunchState (block : Fin (n_boot p)) (cursor : Nat) where
  coordinator : ReferenceActivePhysicalStep.CoordinatorConfiguration p rate
  upDecoderBank : CoordinatorUpReception.UpDecoderBank p
  followers : Fin (p.m - 1) → ActualInitializationPhysicalStep.FollowerState p rate block
  followers_at_cursor : ∀ i, ActualInitializationRun.followerAtCursor p rate block cursor
    (followers i)

/-- A one-round source input. The cursor bound is local typing for the real
block calendar; its time is derived below, never supplied independently. -/
structure PhysicalInput (block : Fin (n_boot p)) (cursor : Nat) where
  source : SourceInput p
  rewards : GridRewardTable p
  state : PostlaunchState (p := p) (rate := rate) block cursor
  cursor_lt : cursor < BootstrapObservedFollower.blockLength p block

/-- The actual calendar time at this clipped-block cursor. -/
def PhysicalInput.time {block : Fin (n_boot p)} {cursor : Nat}
    (input : PhysicalInput (p := p) (rate := rate) block cursor) : Fin p.T :=
  ActualInitializationRun.blockTime p block cursor input.cursor_lt

/-- Cursor preservation makes the existing follower preparation interface
ready at the actual block time. Bootstrap cursor equality and declared
activation bounds are the only inputs used here. -/
theorem follower_ready_at_time {block : Fin (n_boot p)} {cursor : Nat}
    (input : PhysicalInput (p := p) (rate := rate) block cursor)
    (i : Fin (p.m - 1)) :
    ActualInitializationPhysicalStep.followerAtNextCursor input.time
      (input.state.followers i) := by
  cases hf : input.state.followers i with
  | bootstrap startup =>
      have hcursor := input.state.followers_at_cursor i
      rw [hf] at hcursor
      change startup.processed.val = cursor at hcursor
      change input.time ∈ BootstrapDimensions.calendarBlock p block ∧
        startup.processed.val < BootstrapObservedFollower.blockLength p block ∧
        input.time.val = BootstrapObservedFollower.blockStart p block + startup.processed.val
      refine ⟨ActualInitializationRun.blockTime_mem p block cursor input.cursor_lt, ?_, ?_⟩
      · rw [hcursor]
        exact input.cursor_lt
      · simp [PhysicalInput.time, ActualInitializationRun.blockTime, hcursor]
  | declared row activation configuration =>
      have hcursor := input.state.followers_at_cursor i
      rw [hf] at hcursor
      change activation.val ≤ BootstrapObservedFollower.blockStart p block + cursor + 1 at hcursor
      change activation.val ≤ input.time.val + 1
      simpa [PhysicalInput.time, ActualInitializationRun.blockTime] using hcursor

/-- The valid follower preparation respects equality of its retained state;
the readiness proofs are only local typing witnesses. -/
theorem prepareFollowerValid_eq_of_follower_eq {block : Fin (n_boot p)}
    (time : Fin p.T) (source : SourceInput p) (i : Fin (p.m - 1))
    (follower follower' : ActualInitializationPhysicalStep.FollowerState p rate block)
    (hfollowers : follower = follower')
    (hready : ActualInitializationPhysicalStep.followerAtNextCursor time follower)
    (hready' : ActualInitializationPhysicalStep.followerAtNextCursor time follower') :
    ActualInitializationPhysicalStep.prepareFollowerValid rate block time source i follower hready =
      ActualInitializationPhysicalStep.prepareFollowerValid rate block time source i follower' hready' := by
  cases hfollowers
  rfl

/-- The literal coordinator preparation and each follower's actual local
preparation, all at the same source-derived calendar round. -/
structure PreparedRound {block : Fin (n_boot p)} {cursor : Nat}
    (input : PhysicalInput (p := p) (rate := rate) block cursor) where
  coordinator : OrdinaryCoordinatorPhysicalInterface.Preparation rate
    input.state.upDecoderBank
    (input.source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p input.source))
    input.time
  coordinator_eq : coordinator = OrdinaryCoordinatorPhysicalInterface.prepareLocal
    input.state.coordinator input.state.upDecoderBank
    (input.source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p input.source))
    input.time
  followers : Fin (p.m - 1) → ActualInitializationPhysicalStep.PreparedFollower p rate block
  followers_eq : ∀ i, followers i = ActualInitializationPhysicalStep.prepareFollowerValid
    rate block input.time input.source i (input.state.followers i)
      (follower_ready_at_time input i)

/-- Call the coordinator's accepted local PREPARE exactly once and prepare
each follower from its own retained branch and original source coordinates. -/
def prepare {block : Fin (n_boot p)} {cursor : Nat}
    (input : PhysicalInput (p := p) (rate := rate) block cursor) : PreparedRound input :=
  { coordinator := OrdinaryCoordinatorPhysicalInterface.prepareLocal
      input.state.coordinator input.state.upDecoderBank
      (input.source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p input.source))
      input.time
    coordinator_eq := rfl
    followers := fun i => ActualInitializationPhysicalStep.prepareFollowerValid
      rate block input.time input.source i (input.state.followers i)
        (follower_ready_at_time input i)
    followers_eq := fun _ => rfl }

/-- The one simultaneous arm profile, assembled from the retained coordinator
preparation and all original per-follower preparations. -/
def actionProfile {block : Fin (n_boot p)} {cursor : Nat}
    {input : PhysicalInput (p := p) (rate := rate) block cursor}
    (prepared : PreparedRound input) : FiniteBanditModel.ActionProfile p.m p.K :=
  fun player =>
    if hp : player = ActiveRoundActions.coordinator p.two_le_m then
      prepared.coordinator.arm
    else
      (prepared.followers
        (ActiveRoundActions.followerIndex p.two_le_m player hp)).arm

theorem actionProfile_coordinator {block : Fin (n_boot p)} {cursor : Nat}
    {input : PhysicalInput (p := p) (rate := rate) block cursor}
    (prepared : PreparedRound input) :
    actionProfile prepared (ActiveRoundActions.coordinator p.two_le_m) =
      prepared.coordinator.arm := by
  simp [actionProfile]

theorem actionProfile_follower {block : Fin (n_boot p)} {cursor : Nat}
    {input : PhysicalInput (p := p) (rate := rate) block cursor}
    (prepared : PreparedRound input) (i : Fin (p.m - 1)) :
    actionProfile prepared (PublicDiscreteDraws.followerPlayer p.two_le_m i) =
      (prepared.followers i).arm := by
  unfold actionProfile
  rw [dite_eq_right (ActiveRoundActions.followerPlayer_ne_coordinator p.two_le_m i)]
  rw [ActiveRoundActions.followerIndex_followerPlayer p.two_le_m i
    (ActiveRoundActions.followerPlayer_ne_coordinator p.two_le_m i)]

/-- Collision-filtered feedback from the single actual joint profile and the
fixed rounded reward table. -/
def gridFeedback {block : Fin (n_boot p)} {cursor : Nat}
    {input : PhysicalInput (p := p) (rate := rate) block cursor}
    (prepared : PreparedRound input) (player : Fin p.m) : Fin (D p + 1) := by
  classical
  exact if FiniteBanditModel.collisionFreeFor (actionProfile prepared) player then
    input.rewards input.time (actionProfile prepared player) else 0

theorem gridFeedback_eq_zero_of_collision {block : Fin (n_boot p)} {cursor : Nat}
    {input : PhysicalInput (p := p) (rate := rate) block cursor}
    (prepared : PreparedRound input) (player : Fin p.m)
    (hcollision : ¬ FiniteBanditModel.collisionFreeFor (actionProfile prepared) player) :
    gridFeedback prepared player = 0 := by
  classical
  simp [gridFeedback, hcollision]

theorem gridFeedback_eq_reward_of_collision_free {block : Fin (n_boot p)} {cursor : Nat}
    {input : PhysicalInput (p := p) (rate := rate) block cursor}
    (prepared : PreparedRound input) (player : Fin p.m)
    (hfree : FiniteBanditModel.collisionFreeFor (actionProfile prepared) player) :
    gridFeedback prepared player = input.rewards input.time (actionProfile prepared player) := by
  classical
  simp [gridFeedback, hfree]

/-- Each player's feedback entry is the one derived by the physical collision
rule. -/
def physicalFeedback {block : Fin (n_boot p)} {cursor : Nat}
    {input : PhysicalInput (p := p) (rate := rate) block cursor}
    (prepared : PreparedRound input) : Fin p.m → Fin (D p + 1) :=
  gridFeedback prepared

/-- The actual accepted follower result, proved to exist from its own cursor
typing and this follower's physically derived feedback. The selected outcome
is an output of the deterministic observer, never a fallback state. -/
theorem follower_success {block : Fin (n_boot p)} {cursor : Nat}
    {input : PhysicalInput (p := p) (rate := rate) block cursor}
    (prepared : PreparedRound input) (i : Fin (p.m - 1)) :
    ∃ outcome, ActualInitializationPhysicalStep.observeFollower rate block input.time
      input.source i (prepared.followers i)
      (physicalFeedback prepared (PublicDiscreteDraws.followerPlayer p.two_le_m i)) =
        .ok outcome := by
  rw [prepared.followers_eq i]
  exact ActualInitializationPhysicalStep.observeFollower_success_of_state rate block
    input.time input.source i (input.state.followers i) (follower_ready_at_time input i)
    (physicalFeedback prepared (PublicDiscreteDraws.followerPlayer p.two_le_m i))

/-- Deterministic accepted output of one local follower observation. -/
noncomputable def followerOutcome {block : Fin (n_boot p)} {cursor : Nat}
    {input : PhysicalInput (p := p) (rate := rate) block cursor}
    (prepared : PreparedRound input) (i : Fin (p.m - 1)) :
    ActualInitializationPhysicalStep.FollowerOutcome p rate block :=
  Classical.choose (follower_success prepared i)

theorem followerOutcome_eq_observe {block : Fin (n_boot p)} {cursor : Nat}
    {input : PhysicalInput (p := p) (rate := rate) block cursor}
    (prepared : PreparedRound input) (i : Fin (p.m - 1)) :
    ActualInitializationPhysicalStep.observeFollower rate block input.time input.source i
      (prepared.followers i)
      (physicalFeedback prepared (PublicDiscreteDraws.followerPlayer p.two_le_m i)) =
        .ok (followerOutcome prepared i) :=
  Classical.choose_spec (follower_success prepared i)

/-- Any successful local observation advances the actual block cursor for a
bootstrap follower, and preserves activation readiness for a declared one. -/
theorem successful_follower_observation_next_cursor {block : Fin (n_boot p)}
    {cursor : Nat} (time : Fin p.T) (source : SourceInput p)
    (i : Fin (p.m - 1)) (follower : ActualInitializationPhysicalStep.FollowerState p rate block)
    (hcursor : ActualInitializationRun.followerAtCursor p rate block cursor follower)
    (hready : ActualInitializationPhysicalStep.followerAtNextCursor time follower)
    (ownFeedback : Fin (D p + 1))
    (outcome : ActualInitializationPhysicalStep.FollowerOutcome p rate block)
    (htransition : ActualInitializationPhysicalStep.observeFollower rate block time source i
      (ActualInitializationPhysicalStep.prepareFollowerValid rate block time source i follower hready)
      ownFeedback = .ok outcome) :
    ActualInitializationRun.followerAtCursor p rate block (cursor + 1) outcome.next := by
  classical
  cases follower with
  | bootstrap startup =>
      change startup.processed.val = cursor at hcursor
      change time ∈ BootstrapDimensions.calendarBlock p block ∧
        startup.processed.val < BootstrapObservedFollower.blockLength p block ∧
        time.val = BootstrapObservedFollower.blockStart p block + startup.processed.val at hready
      have haccepted := BootstrapObservedFollower.observe_accepted_processed p block startup
        source.1.1 source.1.2 time
        (ActualInitializationPhysicalStep.observationOfGrid p ownFeedback)
        hready.1 hready.2.1 hready.2.2
      simp only [ActualInitializationPhysicalStep.prepareFollowerValid,
        ActualInitializationPhysicalStep.observeFollower, haccepted,
        Except.ok.injEq] at htransition
      cases htransition
      change (BootstrapObservedFollower.observeOne p block startup source.1.1
        source.1.2 time (ActualInitializationPhysicalStep.observationOfGrid p ownFeedback)
        hready.1 hready.2.1 hready.2.2).processed.val = cursor + 1
      rw [BootstrapObservedFollower.observe_accepted_cursor p block startup source.1.1
        source.1.2 time (ActualInitializationPhysicalStep.observationOfGrid p ownFeedback)
        hready.1 hready.2.1 hready.2.2]
      omega
  | declared row activation configuration =>
      change activation.val ≤ BootstrapObservedFollower.blockStart p block + cursor + 1 at hcursor
      simp only [ActualInitializationPhysicalStep.prepareFollowerValid,
        ActualInitializationPhysicalStep.observeFollower, Except.ok.injEq] at htransition
      cases htransition
      simp only [ActualInitializationRun.followerAtCursor]
      omega

/-- A successful bootstrap observation advances its processed cursor once;
declared observation preserves its original row and activation. This proves
the state is ready for the next actual cursor even on local dagger paths. -/
theorem followerOutcome_next_at_cursor {block : Fin (n_boot p)} {cursor : Nat}
    {input : PhysicalInput (p := p) (rate := rate) block cursor}
    (prepared : PreparedRound input) (i : Fin (p.m - 1)) :
    ActualInitializationRun.followerAtCursor p rate block (cursor + 1)
      (followerOutcome prepared i).next := by
  have htransition := followerOutcome_eq_observe prepared i
  rw [prepared.followers_eq i] at htransition
  exact successful_follower_observation_next_cursor input.time input.source i
    (input.state.followers i) (input.state.followers_at_cursor i)
    (follower_ready_at_time input i)
    (physicalFeedback prepared (PublicDiscreteDraws.followerPlayer p.two_le_m i))
    (followerOutcome prepared i) htransition

/-- One actual postlaunch result. Coordinator and follower observations are
the literal accepted local observer outputs after the joint feedback vector
has been derived. -/
structure RoundResult {block : Fin (n_boot p)} {cursor : Nat}
    (input : PhysicalInput (p := p) (rate := rate) block cursor) where
  prepared : PreparedRound input
  coordinatorObservation : ReferenceActivePhysicalStep.CoordinatorObservation p rate
  coordinatorObservation_eq : coordinatorObservation =
    OrdinaryCoordinatorPhysicalInterface.observeLocal prepared.coordinator
      (physicalFeedback prepared (ActiveRoundActions.coordinator p.two_le_m))
  followers : Fin (p.m - 1) → ActualInitializationPhysicalStep.FollowerOutcome p rate block
  followers_eq : ∀ i, followers i = followerOutcome prepared i
  followerTransition : ∀ i,
    ActualInitializationPhysicalStep.observeFollower rate block input.time input.source i
      (prepared.followers i)
      (physicalFeedback prepared (PublicDiscreteDraws.followerPlayer p.two_le_m i)) =
        .ok (followers i)

/-- Apply the retained local observations to only their own derived feedback
entries. No local observer is rerun after this result is assembled. -/
noncomputable def observePrepared {block : Fin (n_boot p)} {cursor : Nat}
    {input : PhysicalInput (p := p) (rate := rate) block cursor}
    (prepared : PreparedRound input) : RoundResult input :=
  { prepared := prepared
    coordinatorObservation := OrdinaryCoordinatorPhysicalInterface.observeLocal
      prepared.coordinator
      (physicalFeedback prepared (ActiveRoundActions.coordinator p.two_le_m))
    coordinatorObservation_eq := rfl
    followers := fun i => followerOutcome prepared i
    followers_eq := fun _ => rfl
    followerTransition := fun i => followerOutcome_eq_observe prepared i }

/-- The actual deterministic mixed physical step. -/
noncomputable def step {block : Fin (n_boot p)} {cursor : Nat}
    (input : PhysicalInput (p := p) (rate := rate) block cursor) : RoundResult input :=
  observePrepared (prepare input)

/-- The next indexed storage contains exactly the local coordinator
configuration/bank and every actual follower output. -/
def RoundResult.nextState {block : Fin (n_boot p)} {cursor : Nat}
    {input : PhysicalInput (p := p) (rate := rate) block cursor}
    (result : RoundResult input) : PostlaunchState (p := p) (rate := rate) block (cursor + 1) :=
  { coordinator := result.coordinatorObservation.configuration
    upDecoderBank := result.coordinatorObservation.upDecoderBank
    followers := fun i => (result.followers i).next
    followers_at_cursor := fun i => by
      rw [result.followers_eq i]
      exact followerOutcome_next_at_cursor result.prepared i }

theorem RoundResult.nextState_coordinator {block : Fin (n_boot p)} {cursor : Nat}
    {input : PhysicalInput (p := p) (rate := rate) block cursor}
    (result : RoundResult input) :
    result.nextState.coordinator = result.coordinatorObservation.configuration := rfl

theorem RoundResult.nextState_bank {block : Fin (n_boot p)} {cursor : Nat}
    {input : PhysicalInput (p := p) (rate := rate) block cursor}
    (result : RoundResult input) :
    result.nextState.upDecoderBank = result.coordinatorObservation.upDecoderBank := rfl

theorem step_next_follower_at_cursor {block : Fin (n_boot p)} {cursor : Nat}
    (input : PhysicalInput (p := p) (rate := rate) block cursor)
    (i : Fin (p.m - 1)) :
    ActualInitializationRun.followerAtCursor p rate block (cursor + 1)
      ((step input).followers i).next := by
  exact followerOutcome_next_at_cursor (step input).prepared i

theorem step_action_coordinator {block : Fin (n_boot p)} {cursor : Nat}
    (input : PhysicalInput (p := p) (rate := rate) block cursor) :
    actionProfile (step input).prepared (ActiveRoundActions.coordinator p.two_le_m) =
      (step input).prepared.coordinator.arm :=
  actionProfile_coordinator _

theorem step_action_follower {block : Fin (n_boot p)} {cursor : Nat}
    (input : PhysicalInput (p := p) (rate := rate) block cursor)
    (i : Fin (p.m - 1)) :
    actionProfile (step input).prepared (PublicDiscreteDraws.followerPlayer p.two_le_m i) =
      ((step input).prepared.followers i).arm :=
  actionProfile_follower _ i

theorem step_feedback_coordinator {block : Fin (n_boot p)} {cursor : Nat}
    (input : PhysicalInput (p := p) (rate := rate) block cursor) :
    physicalFeedback (step input).prepared (ActiveRoundActions.coordinator p.two_le_m) =
      gridFeedback (step input).prepared (ActiveRoundActions.coordinator p.two_le_m) := rfl

theorem step_feedback_follower {block : Fin (n_boot p)} {cursor : Nat}
    (input : PhysicalInput (p := p) (rate := rate) block cursor)
    (i : Fin (p.m - 1)) :
    physicalFeedback (step input).prepared (PublicDiscreteDraws.followerPlayer p.two_le_m i) =
      gridFeedback (step input).prepared (PublicDiscreteDraws.followerPlayer p.two_le_m i) := rfl

theorem step_coordinator_observation {block : Fin (n_boot p)} {cursor : Nat}
    (input : PhysicalInput (p := p) (rate := rate) block cursor) :
    (step input).coordinatorObservation =
      OrdinaryCoordinatorPhysicalInterface.observeLocal (step input).prepared.coordinator
        (physicalFeedback (step input).prepared
          (ActiveRoundActions.coordinator p.two_le_m)) := rfl

theorem step_follower_observation {block : Fin (n_boot p)} {cursor : Nat}
    (input : PhysicalInput (p := p) (rate := rate) block cursor)
    (i : Fin (p.m - 1)) :
    ActualInitializationPhysicalStep.observeFollower rate block input.time input.source i
      ((step input).prepared.followers i)
      (physicalFeedback (step input).prepared
        (PublicDiscreteDraws.followerPlayer p.two_le_m i)) = .ok ((step input).followers i) :=
  (step input).followerTransition i

/-- The exact branch in which every retained follower is declared in the
source-selected row. This is a local case discriminator, not a run-history
assumption or a replacement for mixed play. -/
abbrev AllDeclaredSelectedRow {block : Fin (n_boot p)} {cursor : Nat}
    (input : PhysicalInput (p := p) (rate := rate) block cursor) : Prop :=
  ∀ i, ∃ localState : ReferencePrelaunchFollower.Activation p ×
      DeclaredFollowerLocalRound.LocalConfiguration p rate,
    input.state.followers i = .declared
      (ActualInitializationPhysicalStep.selectedRowIndex p input.source)
      localState.1 localState.2

/-- The canonical branch's activation/configuration pair is read from that
follower's actual retained declared state. The impossible bootstrap branch
uses the witness only to make the function total. -/
noncomputable def canonicalFollowerData {block : Fin (n_boot p)} {cursor : Nat}
    (input : PhysicalInput (p := p) (rate := rate) block cursor)
    (hdeclared : AllDeclaredSelectedRow input) (i : Fin (p.m - 1)) :
    ReferencePrelaunchFollower.Activation p × DeclaredFollowerLocalRound.LocalConfiguration p rate :=
  match input.state.followers i with
  | .bootstrap _ => Classical.choose (hdeclared i)
  | .declared _ activation configuration => (activation, configuration)

/-- Pack the existing canonical ordinary input only on the genuine
all-declared, selected-row branch. Its activation proof is derived from this
input's actual cursor typing. -/
noncomputable def canonicalRoundInput {block : Fin (n_boot p)} {cursor : Nat}
    (input : PhysicalInput (p := p) (rate := rate) block cursor)
    (hdeclared : AllDeclaredSelectedRow input) :
    ReferenceActivePhysicalStep.RoundInput p rate := by
  classical
  refine {
    state := {
      coordinator := input.state.coordinator
      upDecoderBank := input.state.upDecoderBank
      activations := fun i => (canonicalFollowerData input hdeclared i).1
      followers := fun i => (canonicalFollowerData input hdeclared i).2 }
    rows := input.source.1.2
    selected := ActualInitializationPhysicalStep.selectedRowIndex p input.source
    time := input.time
    active := ?_
    rewards := input.rewards }
  intro i
  cases hf : input.state.followers i with
  | bootstrap startup =>
      obtain ⟨localState, hlocal⟩ := hdeclared i
      rw [hf] at hlocal
      cases hlocal
  | declared row activation configuration =>
      have hready := follower_ready_at_time input i
      rw [hf] at hready
      have hactive : activation.val ≤ input.time.val + 1 := by
        simpa [ActualInitializationPhysicalStep.followerAtNextCursor] using hready
      simpa [canonicalFollowerData, hf] using hactive

/-- On the accepted branch above, the constructed canonical input retains the
same row, time, complete reward table, coordinator configuration, and bank. -/
theorem canonicalRoundInput_fields {block : Fin (n_boot p)} {cursor : Nat}
    (input : PhysicalInput (p := p) (rate := rate) block cursor)
    (hdeclared : AllDeclaredSelectedRow input) :
    let x := canonicalRoundInput input hdeclared
    x.row = input.source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p input.source) ∧
      x.time = input.time ∧ x.rewards = input.rewards ∧
      x.state.coordinator = input.state.coordinator ∧
      x.state.upDecoderBank = input.state.upDecoderBank := by
  simp [canonicalRoundInput, ReferenceActivePhysicalStep.RoundInput.row]

/-- The retained coordinator preparation is the same dependent local
preparation as the canonical input, after transporting its exact fields. -/
theorem coordinatorPrepared_eq_canonical {block : Fin (n_boot p)} {cursor : Nat}
    (input : PhysicalInput (p := p) (rate := rate) block cursor)
    (hdeclared : AllDeclaredSelectedRow input) :
    (prepare input).coordinator =
      OrdinaryCoordinatorPhysicalInterface.prepareLocal
        (canonicalRoundInput input hdeclared).state.coordinator
        (canonicalRoundInput input hdeclared).state.upDecoderBank
        (canonicalRoundInput input hdeclared).row
        (canonicalRoundInput input hdeclared).time := by
  rw [(prepare input).coordinator_eq]
  have hfields := canonicalRoundInput_fields input hdeclared
  have hrow : (canonicalRoundInput input hdeclared).row =
      input.source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p input.source) := by
    simpa using hfields.1
  have htime : (canonicalRoundInput input hdeclared).time = input.time := by
    simpa using hfields.2.1
  have hcoordinator : (canonicalRoundInput input hdeclared).state.coordinator =
      input.state.coordinator := by
    simpa using hfields.2.2.2.1
  have hbank : (canonicalRoundInput input hdeclared).state.upDecoderBank =
      input.state.upDecoderBank := by
    simpa using hfields.2.2.2.2
  cases hrow
  cases htime
  cases hcoordinator
  cases hbank
  rfl

/-- A selected-row declared follower has exactly the canonical local PREPARE
result, with no condition on its ordinary or dagger configuration. -/
theorem canonical_preparedFollower_round {block : Fin (n_boot p)} {cursor : Nat}
    (input : PhysicalInput (p := p) (rate := rate) block cursor)
    (hdeclared : AllDeclaredSelectedRow input) (i : Fin (p.m - 1)) :
    (prepare input).followers i =
      .declared (ActualInitializationPhysicalStep.selectedRowIndex p input.source)
        (canonicalFollowerData input hdeclared i).1
        ((ReferenceActivePhysicalStep.prepare
          (canonicalRoundInput input hdeclared)).followers.followers i) := by
  classical
  let x := canonicalRoundInput input hdeclared
  cases hf : input.state.followers i with
  | bootstrap startup =>
      obtain ⟨localState, hlocal⟩ := hdeclared i
      rw [hf] at hlocal
      cases hlocal
  | declared row activation configuration =>
      obtain ⟨localState, hlocal⟩ := hdeclared i
      rw [hf] at hlocal
      injection hlocal with hrow hactivation hconfiguration
      cases hrow
      have hready := follower_ready_at_time input i
      rw [hf] at hready
      have hactive : activation.val ≤ input.time.val + 1 := by
        simpa [ActualInitializationPhysicalStep.followerAtNextCursor] using hready
      have hactual : (prepare input).followers i =
          .declared (ActualInitializationPhysicalStep.selectedRowIndex p input.source)
            activation
            (DeclaredFollowerLocalRound.prepare rate i
              (input.source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p input.source))
              activation input.time hactive configuration) := by
        calc
          (prepare input).followers i =
              ActualInitializationPhysicalStep.prepareFollowerValid rate block input.time
                input.source i (input.state.followers i) (follower_ready_at_time input i) :=
            (prepare input).followers_eq i
          _ = ActualInitializationPhysicalStep.prepareFollowerValid rate block input.time
                input.source i
                (.declared (ActualInitializationPhysicalStep.selectedRowIndex p input.source)
                  activation configuration) hready :=
            prepareFollowerValid_eq_of_follower_eq input.time input.source i
              (input.state.followers i)
              (.declared (ActualInitializationPhysicalStep.selectedRowIndex p input.source)
                activation configuration) hf (follower_ready_at_time input i) hready
          _ = .declared (ActualInitializationPhysicalStep.selectedRowIndex p input.source)
                activation
                (DeclaredFollowerLocalRound.prepare rate i
                  (input.source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p input.source))
                  activation input.time hactive configuration) := rfl
      have hcanonical :
          (ReferenceActivePhysicalStep.prepare x).followers.followers i =
            DeclaredFollowerLocalRound.prepare rate i
              (input.source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p input.source))
              activation input.time hactive configuration := by
        change ReferenceActiveFeedbackCut.prepareFollowers
          (ReferenceActivePhysicalStep.followerInput x) i = _
        rw [ReferenceActiveFeedbackCut.prepareFollowers_apply]
        simp [ReferenceActivePhysicalStep.followerInput, x, canonicalRoundInput,
          canonicalFollowerData, hf]
      rw [hactual, hcanonical]
      simp [canonicalFollowerData, hf]

/-- The canonical local preparation retains the same action. -/
theorem canonical_preparedFollower_arm {block : Fin (n_boot p)} {cursor : Nat}
    (input : PhysicalInput (p := p) (rate := rate) block cursor)
    (hdeclared : AllDeclaredSelectedRow input) (i : Fin (p.m - 1)) :
    ((prepare input).followers i).arm =
      ((ReferenceActivePhysicalStep.prepare (canonicalRoundInput input hdeclared)).followers.followers i).arm := by
  rw [canonical_preparedFollower_round input hdeclared i]
  rfl

/-- The same prepared arms are used by the actual mixed profile and the
existing canonical coordinator/follower action input. -/
theorem actionProfile_eq_canonical {block : Fin (n_boot p)} {cursor : Nat}
    (input : PhysicalInput (p := p) (rate := rate) block cursor)
    (hdeclared : AllDeclaredSelectedRow input) :
    actionProfile (prepare input) =
      (ReferenceActivePhysicalStep.prepare (canonicalRoundInput input hdeclared)).arms.actions := by
  classical
  let x := canonicalRoundInput input hdeclared
  have hcoordinator : (prepare input).coordinator.arm =
      (ReferenceActivePhysicalStep.prepare x).coordinator.arm := by
    rw [coordinatorPrepared_eq_canonical input hdeclared]
    exact OrdinaryCoordinatorPhysicalInterface.prepareLocal_arm x
  change actionProfile (prepare input) =
    (ReferenceActivePhysicalStep.prepare x).arms.actions
  funext player
  by_cases hp : player = ActiveRoundActions.coordinator p.two_le_m
  · simp [actionProfile, hp, ReferenceActivePhysicalStep.PreparedRound.arms,
      ReferenceActiveFeedbackCut.ActionInputs.actions, hcoordinator]
  · let i := ActiveRoundActions.followerIndex p.two_le_m player hp
    have hi : ((prepare input).followers i).arm =
        ((ReferenceActivePhysicalStep.prepare x).followers.followers i).arm :=
      canonical_preparedFollower_arm input hdeclared i
    simp [actionProfile, hp, i, ReferenceActivePhysicalStep.PreparedRound.arms,
      ReferenceActiveFeedbackCut.ActionInputs.actions, hi]

/-- The derived mixed feedback equals the canonical collision-filtered vector
on the same all-declared selected-row branch. -/
theorem gridFeedback_eq_canonical {block : Fin (n_boot p)} {cursor : Nat}
    (input : PhysicalInput (p := p) (rate := rate) block cursor)
    (hdeclared : AllDeclaredSelectedRow input) (player : Fin p.m) :
    gridFeedback (prepare input) player =
      (ReferenceActivePhysicalStep.prepare (canonicalRoundInput input hdeclared)).feedback.feedback player := by
  classical
  let x := canonicalRoundInput input hdeclared
  have hprofile := actionProfile_eq_canonical input hdeclared
  change (if FiniteBanditModel.collisionFreeFor (actionProfile (prepare input)) player then
      input.rewards input.time (actionProfile (prepare input) player) else 0) =
    (ReferenceActivePhysicalStep.prepare x).feedback.feedback player
  rw [hprofile]
  change (if FiniteBanditModel.collisionFreeFor
      (ReferenceActivePhysicalStep.prepare x).arms.actions player then
        x.rewards x.time ((ReferenceActivePhysicalStep.prepare x).arms.actions player)
      else 0) = (ReferenceActivePhysicalStep.prepare x).feedback.feedback player
  have hrule := (ReferenceActivePhysicalStep.prepare x).feedback.feedback_collision_rule player
  have hactions : (ReferenceActivePhysicalStep.prepare x).feedback.actions =
      (ReferenceActivePhysicalStep.prepare x).arms.actions := by
    change (ReferenceActivePhysicalStep.prepare x).feedback.armInputs.actions = _
    rw [(ReferenceActivePhysicalStep.prepare x).feedback.armInputs_eq]
  calc
    (if FiniteBanditModel.collisionFreeFor
        (ReferenceActivePhysicalStep.prepare x).arms.actions player then
          x.rewards x.time ((ReferenceActivePhysicalStep.prepare x).arms.actions player)
        else 0) =
      (if FiniteBanditModel.collisionFreeFor
          (ReferenceActivePhysicalStep.prepare x).feedback.actions player then
            x.rewards x.time ((ReferenceActivePhysicalStep.prepare x).feedback.actions player)
          else 0) := by rw [← hactions]
    _ = (ReferenceActivePhysicalStep.prepare x).feedback.feedback player := hrule.symm

/-- Full coordinator observation specialization, including its exact failure,
recorder, diagnostic, configuration, and decoder-bank result, with the
feedback derived from the actual profile above. -/
theorem coordinatorObservation_eq_canonical {block : Fin (n_boot p)} {cursor : Nat}
    (input : PhysicalInput (p := p) (rate := rate) block cursor)
    (hdeclared : AllDeclaredSelectedRow input) :
    OrdinaryCoordinatorPhysicalInterface.observeLocal (prepare input).coordinator
        (physicalFeedback (prepare input) (ActiveRoundActions.coordinator p.two_le_m)) =
      OrdinaryActivePhysicalStep.observeCoordinator
        (ReferenceActivePhysicalStep.prepare (canonicalRoundInput input hdeclared)) := by
  let x := canonicalRoundInput input hdeclared
  rw [coordinatorPrepared_eq_canonical input hdeclared]
  change OrdinaryCoordinatorPhysicalInterface.observeLocal
      (OrdinaryCoordinatorPhysicalInterface.prepareLocal
        x.state.coordinator x.state.upDecoderBank x.row x.time)
      (gridFeedback (prepare input) (ActiveRoundActions.coordinator p.two_le_m)) = _
  rw [gridFeedback_eq_canonical input hdeclared (ActiveRoundActions.coordinator p.two_le_m)]
  rw [← show (ReferenceActivePhysicalStep.prepare x).coordinatorObservation =
      (ReferenceActivePhysicalStep.prepare x).feedback.feedback
        (ActiveRoundActions.coordinator p.two_le_m) by rfl]
  exact OrdinaryCoordinatorPhysicalInterface.observeLocal_prepareLocal x

/-- Public projections of the canonical coordinator specialization through
the existing ordinary `step`, retaining the complete failure/bank/recorder
outputs even when any local operation rejects. -/
theorem coordinatorFields_eq_canonical_step {block : Fin (n_boot p)} {cursor : Nat}
    (input : PhysicalInput (p := p) (rate := rate) block cursor)
    (hdeclared : AllDeclaredSelectedRow input) :
    let x := canonicalRoundInput input hdeclared
    (OrdinaryCoordinatorPhysicalInterface.observeLocal (prepare input).coordinator
      (physicalFeedback (prepare input) (ActiveRoundActions.coordinator p.two_le_m))).configuration =
        (OrdinaryActivePhysicalStep.step x).next.coordinator ∧
    (OrdinaryCoordinatorPhysicalInterface.observeLocal (prepare input).coordinator
      (physicalFeedback (prepare input) (ActiveRoundActions.coordinator p.two_le_m))).upDecoderBank =
        (OrdinaryActivePhysicalStep.step x).next.upDecoderBank ∧
    (OrdinaryCoordinatorPhysicalInterface.observeLocal (prepare input).coordinator
      (physicalFeedback (prepare input) (ActiveRoundActions.coordinator p.two_le_m))).recording =
        (OrdinaryActivePhysicalStep.step x).coordinator.recording ∧
    (OrdinaryCoordinatorPhysicalInterface.observeLocal (prepare input).coordinator
      (physicalFeedback (prepare input) (ActiveRoundActions.coordinator p.two_le_m))).failure =
        (OrdinaryActivePhysicalStep.step x).coordinator.failure := by
  let x := canonicalRoundInput input hdeclared
  rw [coordinatorObservation_eq_canonical input hdeclared]
  rw [← OrdinaryCoordinatorPhysicalInterface.observeLocal_prepareLocal x]
  exact OrdinaryCoordinatorPhysicalInterface.observeLocal_prepareLocal_fields x

/-- The full declared follower successor agrees with the ordinary canonical
step, including ordinary failure and dagger outcomes. -/
theorem followerNext_eq_canonical_step {block : Fin (n_boot p)} {cursor : Nat}
    (input : PhysicalInput (p := p) (rate := rate) block cursor)
    (hdeclared : AllDeclaredSelectedRow input) (i : Fin (p.m - 1)) :
    ((step input).followers i).next =
      .declared (ActualInitializationPhysicalStep.selectedRowIndex p input.source)
        (canonicalFollowerData input hdeclared i).1
        ((OrdinaryActivePhysicalStep.step
          (canonicalRoundInput input hdeclared)).next.followers i) := by
  let x := canonicalRoundInput input hdeclared
  let player := PublicDiscreteDraws.followerPlayer p.two_le_m i
  have hprepared := canonical_preparedFollower_round input hdeclared i
  have hgrid : physicalFeedback (prepare input) player =
      (ReferenceActivePhysicalStep.prepare x).feedback.feedback player := by
    change gridFeedback (prepare input) player = _
    exact gridFeedback_eq_canonical input hdeclared player
  have hobservation : ActualInitializationPhysicalStep.observationOfGrid p
        (physicalFeedback (prepare input) player) =
      (ReferenceActivePhysicalStep.prepare x).feedback.observations player := by
    rw [hgrid, ← (ReferenceActivePhysicalStep.prepare x).feedback.observations_eq player]
  have htransition := (step input).followerTransition i
  change ActualInitializationPhysicalStep.observeFollower rate block input.time input.source i
      ((prepare input).followers i) (physicalFeedback (prepare input) player) =
        .ok ((step input).followers i) at htransition
  rw [hprepared] at htransition
  simp only [ActualInitializationPhysicalStep.observeFollower_declared_eq] at htransition
  rw [hobservation] at htransition
  have hnext := congrArg ActualInitializationPhysicalStep.FollowerOutcome.next
    (Except.ok.inj htransition)
  have hcanonicalNext := (OrdinaryActivePhysicalStep.step_next_fields x).2.2.2 i
  rw [hcanonicalNext]
  exact hnext.symm

/-- The literal accepted boundary output of one follower at a completed
actual block cursor. -/
def boundaryOutput {block : Fin (n_boot p)}
    (state : PostlaunchState (p := p) (rate := rate) block
      (BootstrapObservedFollower.blockLength p block))
    (i : Fin (p.m - 1)) :
    ActualInitializationPhysicalStep.BoundaryFollowerOutput p rate :=
  ActualInitializationRun.boundaryOutputAtCursor p rate block (state.followers i)
    (state.followers_at_cursor i)

/-- The existing local boundary operation accepts each output from its
completed own cursor, including declaration and continuation branches. -/
theorem boundaryOutput_accepted {block : Fin (n_boot p)}
    (state : PostlaunchState (p := p) (rate := rate) block
      (BootstrapObservedFollower.blockLength p block))
    (i : Fin (p.m - 1)) :
    ActualInitializationPhysicalStep.boundaryFollower rate block (state.followers i) =
      .ok (boundaryOutput state i) :=
  ActualInitializationRun.boundaryOutputAtCursor_step p rate block
    (state.followers i) (state.followers_at_cursor i)

/-- Convert the actual boundary result into the already accepted carry
carrier. -/
def boundaryCarry {block : Fin (n_boot p)}
    (state : PostlaunchState (p := p) (rate := rate) block
      (BootstrapObservedFollower.blockLength p block))
    (i : Fin (p.m - 1)) : ActualInitializationRun.FollowerCarry p rate :=
  ActualInitializationRun.followerCarryOfBoundaryOutput rate (boundaryOutput state i)

theorem boundaryCarry_eq_actual_boundary {block : Fin (n_boot p)}
    (state : PostlaunchState (p := p) (rate := rate) block
      (BootstrapObservedFollower.blockLength p block))
    (i : Fin (p.m - 1)) :
    boundaryCarry state i = ActualInitializationRun.followerCarryAtBlockBoundary p rate block
      (state.followers i) := by
  rfl

/-- The next block's follower-only adapter. Bootstrap carries consume the
next block's original private triple; declared rows, activation, and complete
ordinary/dagger configurations are copied by `beginFollowerBlock`. -/
def beginSuccessorFollower {block next : Fin (n_boot p)}
    (hnext : block.val + 1 < n_boot p)
    (hnext_eq : next = ActualInitializationRun.successorBlock p block hnext)
    (source : SourceInput p)
    (state : PostlaunchState (p := p) (rate := rate) block
      (BootstrapObservedFollower.blockLength p block))
    (i : Fin (p.m - 1)) : ActualInitializationPhysicalStep.FollowerState p rate next := by
  subst next
  exact ActualInitializationRun.beginFollowerBlock p rate
    (ActualInitializationRun.successorBlock p block hnext) source i (boundaryCarry state i)

/-- A completed block followed by a genuine successor produces a cursor-zero
ready follower family. No coordinator boundary transition is rerun. -/
theorem beginSuccessorFollower_at_cursor_zero {block next : Fin (n_boot p)}
    (hnext : block.val + 1 < n_boot p)
    (hnext_eq : next = ActualInitializationRun.successorBlock p block hnext)
    (source : SourceInput p)
    (state : PostlaunchState (p := p) (rate := rate) block
      (BootstrapObservedFollower.blockLength p block))
    (i : Fin (p.m - 1)) :
    ActualInitializationRun.followerAtCursor p rate next 0
      (beginSuccessorFollower hnext hnext_eq source state i) := by
  subst next
  have hactivation : (BootstrapObservedFollower.nextActivationRound p block).val =
      BootstrapObservedFollower.blockStart p
        (ActualInitializationRun.successorBlock p block hnext) + 1 := by
    simpa [ActualInitializationRun.successorBlock,
      BootstrapObservedFollower.blockStart] using
      BootstrapObservedFollower.nextActivationRound_nonlast_eq_nextStart p block hnext
  have hstop : BootstrapObservedFollower.blockStop p block =
      BootstrapObservedFollower.blockStart p
        (ActualInitializationRun.successorBlock p block hnext) := by
    change BootstrapObservedFollower.blockStop p block + 1 = _ at hactivation
    omega
  cases hf : state.followers i with
  | bootstrap startup =>
      have hcomplete := state.followers_at_cursor i
      rw [hf] at hcomplete
      change startup.processed.val = BootstrapObservedFollower.blockLength p block at hcomplete
      cases hpending : BootstrapObservedFollower.pendingDeclaration startup.blockCase with
      | none =>
          simp [beginSuccessorFollower, boundaryCarry, boundaryOutput,
            ActualInitializationRun.boundaryOutputAtCursor,
            ActualInitializationRun.boundaryOutputFromFollower, hf, hpending,
            ActualInitializationRun.followerCarryOfBoundaryOutput,
            ActualInitializationRun.beginFollowerBlock,
            BootstrapObservedFollower.beginBlock,
            ActualInitializationRun.followerAtCursor]
          by_cases hactive : PrivateSourceStreams.activityScalarDraw p
              (source.2.1.1 (ActualInitializationRun.successorBlock p block hnext) i).1 = true <;>
            simp [hactive]
      | some row =>
          have hactivation_le :
              (BootstrapObservedFollower.nextActivationRound p block).val ≤
                BootstrapObservedFollower.blockStart p
                  (ActualInitializationRun.successorBlock p block hnext) + 1 := by
            rw [hactivation]
          simp [beginSuccessorFollower, boundaryCarry, boundaryOutput,
            ActualInitializationRun.boundaryOutputAtCursor,
            ActualInitializationRun.boundaryOutputFromFollower, hf, hpending,
            ActualInitializationRun.followerCarryOfBoundaryOutput,
            ActualInitializationRun.beginFollowerBlock,
            ActualInitializationRun.followerAtCursor, hactivation_le]
  | declared row activation configuration =>
      have hcomplete := state.followers_at_cursor i
      rw [hf] at hcomplete
      change activation.val ≤ BootstrapObservedFollower.blockStart p block +
        BootstrapObservedFollower.blockLength p block + 1 at hcomplete
      have hlength : BootstrapObservedFollower.blockStart p block +
          BootstrapObservedFollower.blockLength p block =
            BootstrapObservedFollower.blockStop p block := by
        simp [BootstrapObservedFollower.blockLength]
        have hstart := BootstrapObservedFollower.blockStart_lt_blockStop p block
        omega
      have hready : activation.val ≤ BootstrapObservedFollower.blockStart p
          (ActualInitializationRun.successorBlock p block hnext) + 1 := by
        rw [hlength, hstop] at hcomplete
        exact hcomplete
      simp [beginSuccessorFollower, boundaryCarry, boundaryOutput,
        ActualInitializationRun.boundaryOutputAtCursor,
        ActualInitializationRun.boundaryOutputFromFollower, hf,
        ActualInitializationRun.followerCarryOfBoundaryOutput,
        ActualInitializationRun.beginFollowerBlock,
        ActualInitializationRun.followerAtCursor, hready]

/-- Carry the ordinary coordinator and its decoder bank unchanged while the
real successor block initializes only its heterogeneous follower family. -/
def crossSuccessorBoundary {block next : Fin (n_boot p)}
    (hnext : block.val + 1 < n_boot p)
    (hnext_eq : next = ActualInitializationRun.successorBlock p block hnext)
    (source : SourceInput p)
    (state : PostlaunchState (p := p) (rate := rate) block
      (BootstrapObservedFollower.blockLength p block)) :
    PostlaunchState (p := p) (rate := rate) next 0 := by
  subst next
  exact {
    coordinator := state.coordinator
    upDecoderBank := state.upDecoderBank
    followers := fun i => beginSuccessorFollower hnext rfl source state i
    followers_at_cursor := fun i => beginSuccessorFollower_at_cursor_zero
      hnext rfl source state i }

theorem crossSuccessorBoundary_coordinator {block next : Fin (n_boot p)}
    (hnext : block.val + 1 < n_boot p)
    (hnext_eq : next = ActualInitializationRun.successorBlock p block hnext)
    (source : SourceInput p)
    (state : PostlaunchState (p := p) (rate := rate) block
      (BootstrapObservedFollower.blockLength p block)) :
    (crossSuccessorBoundary hnext hnext_eq source state).coordinator = state.coordinator := by
  cases hnext_eq
  rfl

theorem crossSuccessorBoundary_bank {block next : Fin (n_boot p)}
    (hnext : block.val + 1 < n_boot p)
    (hnext_eq : next = ActualInitializationRun.successorBlock p block hnext)
    (source : SourceInput p)
    (state : PostlaunchState (p := p) (rate := rate) block
      (BootstrapObservedFollower.blockLength p block)) :
    (crossSuccessorBoundary hnext hnext_eq source state).upDecoderBank =
      state.upDecoderBank := by
  cases hnext_eq
  rfl

/-- If H's actual source-initialized run ends at a launch boundary strictly
before `T`, that boundary is nonfinal and has its original successor block. -/
theorem sourceInitializedRun_launch_has_successor (p : Parameters)
    (rate : RateInput p) (source : SourceInput p) (rewards : GridRewardTable p)
    (C_star C_h : ℝ) (launch : BootstrapCoordinatorLocalRound.LaunchedBlock p)
    (learnerSeed : ActualInitializationRun.CoordinatorLearnerZeroSeed p)
    (hlaunch : (ActualInitializationHorizon.sourceInitializedRun p rate source rewards
      C_star C_h).terminalDisposition = .launched launch learnerSeed)
    (hbefore : launch.monitor.launchPosition < p.T) :
    (ActualInitializationHorizon.sourceInitializedRun p rate source rewards
      C_star C_h).terminalBlock.val + 1 < n_boot p := by
  let run := ActualInitializationHorizon.sourceInitializedRun p rate source rewards C_star C_h
  have hstrict := ActualInitializationHorizon.sourceInitializedRun_terminal_launch_strict
    p rate source rewards C_star C_h launch learnerSeed hlaunch
  rcases hstrict with ⟨_, _, _, hposition⟩
  by_cases hnext : run.terminalBlock.val + 1 < n_boot p
  · exact hnext
  · have hterminal := run.terminalBlock.isLt
    have hlast : run.terminalBlock.val + 1 = n_boot p := by omega
    have hstop := BootstrapObservedFollower.finalBlock_endpoint_eq_T p run.terminalBlock hlast
    change launch.monitor.launchPosition = BootstrapObservedFollower.blockStop p run.terminalBlock
      at hposition
    rw [hstop] at hposition
    omega

/-- The original successor block selected by a genuine pre-horizon launch. -/
def sourceInitializedLaunchSuccessorBlock (p : Parameters) (rate : RateInput p)
    (source : SourceInput p) (rewards : GridRewardTable p) (C_star C_h : ℝ)
    (launch : BootstrapCoordinatorLocalRound.LaunchedBlock p)
    (learnerSeed : ActualInitializationRun.CoordinatorLearnerZeroSeed p)
    (hlaunch : (ActualInitializationHorizon.sourceInitializedRun p rate source rewards
      C_star C_h).terminalDisposition = .launched launch learnerSeed)
    (hbefore : launch.monitor.launchPosition < p.T) : Fin (n_boot p) :=
  ActualInitializationRun.successorBlock p
    (ActualInitializationHorizon.sourceInitializedRun p rate source rewards C_star C_h).terminalBlock
    (sourceInitializedRun_launch_has_successor p rate source rewards C_star C_h
      launch learnerSeed hlaunch hbefore)

private theorem sourceInitializedRun_terminalFollowerOutput_eq (p : Parameters)
    (rate : RateInput p) (source : SourceInput p) (rewards : GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) :
    let run := ActualInitializationHorizon.sourceInitializedRun p rate source rewards C_star C_h
    run.terminalHandoff.followers i =
      ActualInitializationRun.boundaryOutputAtCursor p rate run.terminalBlock
        (run.terminalFold.followers i)
        (by
          have hcursor := run.terminalFold.invariant.2.2.1 i
          simpa [run.terminalFold.consumed_eq_blockLength] using hcursor) := by
  let run := ActualInitializationHorizon.sourceInitializedRun p rate source rewards C_star C_h
  have hcomplete : ActualInitializationRun.followerAtCursor p rate run.terminalBlock
      (BootstrapObservedFollower.blockLength p run.terminalBlock)
      (run.terminalFold.followers i) := by
    have hcursor := run.terminalFold.invariant.2.2.1 i
    simpa [run.terminalFold.consumed_eq_blockLength] using hcursor
  have hboundary := ActualInitializationRun.boundaryOutputAtCursor_step p rate
    run.terminalBlock (run.terminalFold.followers i) hcomplete
  have houtputs := ActualInitializationHorizon.combinedBoundaryHandoff_follower_step
    run.terminalFold i
  rw [← run.terminalHandoff_eq] at houtputs
  change ActualInitializationPhysicalStep.boundaryFollower rate run.terminalBlock
      (run.terminalFold.followers i) = .ok (run.terminalHandoff.followers i) at houtputs
  rw [hboundary] at houtputs
  exact (Except.ok.inj houtputs).symm

/-- Begin each launched follower from H's exact terminal boundary output and
the next block's original private scalar triple, when that follower remains a
bootstrap carry. Declared carries are copied whole by `beginFollowerBlock`. -/
def sourceInitializedLaunchedFollower (p : Parameters) (rate : RateInput p)
    (source : SourceInput p) (rewards : GridRewardTable p) (C_star C_h : ℝ)
    (launch : BootstrapCoordinatorLocalRound.LaunchedBlock p)
    (learnerSeed : ActualInitializationRun.CoordinatorLearnerZeroSeed p)
    (hlaunch : (ActualInitializationHorizon.sourceInitializedRun p rate source rewards
      C_star C_h).terminalDisposition = .launched launch learnerSeed)
    (hbefore : launch.monitor.launchPosition < p.T) (i : Fin (p.m - 1)) :
    ActualInitializationPhysicalStep.FollowerState p rate
      (sourceInitializedLaunchSuccessorBlock p rate source rewards C_star C_h
        launch learnerSeed hlaunch hbefore) := by
  let run := ActualInitializationHorizon.sourceInitializedRun p rate source rewards C_star C_h
  exact ActualInitializationRun.beginFollowerBlock p rate
    (sourceInitializedLaunchSuccessorBlock p rate source rewards C_star C_h
      launch learnerSeed hlaunch hbefore)
    source i
    (ActualInitializationRun.followerCarryOfBoundaryOutput rate
      (run.terminalHandoff.followers i))

/-- The real launched boundary outputs produce cursor-zero-ready followers
for the first postlaunch source round. -/
theorem sourceInitializedLaunchedFollower_at_cursor_zero (p : Parameters)
    (rate : RateInput p) (source : SourceInput p) (rewards : GridRewardTable p)
    (C_star C_h : ℝ) (launch : BootstrapCoordinatorLocalRound.LaunchedBlock p)
    (learnerSeed : ActualInitializationRun.CoordinatorLearnerZeroSeed p)
    (hlaunch : (ActualInitializationHorizon.sourceInitializedRun p rate source rewards
      C_star C_h).terminalDisposition = .launched launch learnerSeed)
    (hbefore : launch.monitor.launchPosition < p.T) (i : Fin (p.m - 1)) :
    ActualInitializationRun.followerAtCursor p rate
      (sourceInitializedLaunchSuccessorBlock p rate source rewards C_star C_h
        launch learnerSeed hlaunch hbefore) 0
      (sourceInitializedLaunchedFollower p rate source rewards C_star C_h
        launch learnerSeed hlaunch hbefore i) := by
  let run := ActualInitializationHorizon.sourceInitializedRun p rate source rewards C_star C_h
  let block := run.terminalBlock
  let next := sourceInitializedLaunchSuccessorBlock p rate source rewards C_star C_h
    launch learnerSeed hlaunch hbefore
  have hnext := sourceInitializedRun_launch_has_successor p rate source rewards C_star C_h
    launch learnerSeed hlaunch hbefore
  have hblockStart : BootstrapObservedFollower.blockStart p next =
      (block.val + 1) * B_boot p := by
    change BootstrapObservedFollower.blockStart p
      (ActualInitializationRun.successorBlock p block hnext) = _
    simp [ActualInitializationRun.successorBlock, BootstrapObservedFollower.blockStart]
  have hstart : BootstrapObservedFollower.blockStop p block =
      BootstrapObservedFollower.blockStart p next := by
    have hactivation := BootstrapObservedFollower.nextActivationRound_nonlast_eq_nextStart
      p block hnext
    change BootstrapObservedFollower.blockStop p block + 1 =
      (block.val + 1) * B_boot p + 1 at hactivation
    rw [← hblockStart] at hactivation
    omega
  have hcarry : ActualInitializationRun.followerCarryOfBoundaryOutput rate
      (run.terminalHandoff.followers i) =
      ActualInitializationRun.followerCarryOfBoundaryOutput rate
        (ActualInitializationRun.boundaryOutputFromFollower p rate block
          (run.terminalFold.followers i)) := by
    rw [sourceInitializedRun_terminalFollowerOutput_eq p rate source rewards C_star C_h i]
    rfl
  change ActualInitializationRun.followerAtCursor p rate next 0
    (ActualInitializationRun.beginFollowerBlock p rate next source i
      (ActualInitializationRun.followerCarryOfBoundaryOutput rate (run.terminalHandoff.followers i)))
  rw [hcarry]
  cases hf : run.terminalFold.followers i with
  | bootstrap startup =>
      cases hpending : BootstrapObservedFollower.pendingDeclaration startup.blockCase with
      | none =>
          by_cases hactive : PrivateSourceStreams.activityScalarDraw p
              (source.2.1.1 next i).1 = true <;>
            simp [next, block, run,
              ActualInitializationRun.beginFollowerBlock,
              ActualInitializationRun.followerCarryOfBoundaryOutput,
              ActualInitializationRun.boundaryOutputFromFollower,
              BootstrapObservedFollower.beginBlock,
              ActualInitializationRun.followerAtCursor, hpending, hactive]
      | some row =>
          have hactivation :
              (BootstrapObservedFollower.nextActivationRound p block).val ≤
                BootstrapObservedFollower.blockStart p next + 1 := by
            rw [BootstrapObservedFollower.nextActivationRound_nonlast_eq_nextStart p block hnext,
              hblockStart]
          simp [next, block, run,
            ActualInitializationRun.beginFollowerBlock,
            ActualInitializationRun.followerCarryOfBoundaryOutput,
            ActualInitializationRun.boundaryOutputFromFollower,
            ActualInitializationRun.followerAtCursor, hpending, hactivation]
  | declared row activation configuration =>
      have hcursor := run.terminalFold.invariant.2.2.1 i
      have hready : activation.val ≤ BootstrapObservedFollower.blockStart p next + 1 := by
        have hblockCursor : activation.val ≤ BootstrapObservedFollower.blockStart p block +
            BootstrapObservedFollower.blockLength p block + 1 := by
          simpa [ActualInitializationRun.followerAtCursor, hf,
            run.terminalFold.consumed_eq_blockLength] using hcursor
        rw [ActualInitializationRun.blockStart_add_length_eq_stop] at hblockCursor
        rw [hstart] at hblockCursor
        exact hblockCursor
      simp [next,
        ActualInitializationRun.beginFollowerBlock,
        ActualInitializationRun.followerCarryOfBoundaryOutput,
        ActualInitializationRun.boundaryOutputFromFollower,
        ActualInitializationRun.followerAtCursor, hready]

/-- Construct the actual first postlaunch physical input from H's launched
terminal handoff. The original source and reward table remain whole; only
bootstrap carries read their own next-block private triples. -/
def sourceInitializedLaunchSuccessorInput (p : Parameters) (rate : RateInput p)
    (source : SourceInput p) (rewards : GridRewardTable p) (C_star C_h : ℝ)
    (launch : BootstrapCoordinatorLocalRound.LaunchedBlock p)
    (learnerSeed : ActualInitializationRun.CoordinatorLearnerZeroSeed p)
    (hlaunch : (ActualInitializationHorizon.sourceInitializedRun p rate source rewards
      C_star C_h).terminalDisposition = .launched launch learnerSeed)
    (hbefore : launch.monitor.launchPosition < p.T) :
    PhysicalInput (p := p) (rate := rate)
      (sourceInitializedLaunchSuccessorBlock p rate source rewards C_star C_h
        launch learnerSeed hlaunch hbefore) 0 := by
  let next := sourceInitializedLaunchSuccessorBlock p rate source rewards C_star C_h
    launch learnerSeed hlaunch hbefore
  have hpositive : 0 < BootstrapObservedFollower.blockLength p next := by
    unfold BootstrapObservedFollower.blockLength
    exact Nat.sub_pos_of_lt (BootstrapObservedFollower.blockStart_lt_blockStop p next)
  refine {
    source := source
    rewards := rewards
    state := {
      coordinator := .first
      upDecoderBank := CoordinatorUpReception.initialUpDecoderBank p
      followers := fun i => sourceInitializedLaunchedFollower p rate source rewards C_star C_h
        launch learnerSeed hlaunch hbefore i
      followers_at_cursor := fun i => sourceInitializedLaunchedFollower_at_cursor_zero
        p rate source rewards C_star C_h launch learnerSeed hlaunch hbefore i }
    cursor_lt := hpositive }

theorem sourceInitializedLaunchSuccessorInput_source (p : Parameters)
    (rate : RateInput p) (source : SourceInput p) (rewards : GridRewardTable p)
    (C_star C_h : ℝ) (launch : BootstrapCoordinatorLocalRound.LaunchedBlock p)
    (learnerSeed : ActualInitializationRun.CoordinatorLearnerZeroSeed p)
    (hlaunch : (ActualInitializationHorizon.sourceInitializedRun p rate source rewards
      C_star C_h).terminalDisposition = .launched launch learnerSeed)
    (hbefore : launch.monitor.launchPosition < p.T) :
    (sourceInitializedLaunchSuccessorInput p rate source rewards C_star C_h
      launch learnerSeed hlaunch hbefore).source = source := rfl

theorem sourceInitializedLaunchSuccessorInput_rewards (p : Parameters)
    (rate : RateInput p) (source : SourceInput p) (rewards : GridRewardTable p)
    (C_star C_h : ℝ) (launch : BootstrapCoordinatorLocalRound.LaunchedBlock p)
    (learnerSeed : ActualInitializationRun.CoordinatorLearnerZeroSeed p)
    (hlaunch : (ActualInitializationHorizon.sourceInitializedRun p rate source rewards
      C_star C_h).terminalDisposition = .launched launch learnerSeed)
    (hbefore : launch.monitor.launchPosition < p.T) :
    (sourceInitializedLaunchSuccessorInput p rate source rewards C_star C_h
      launch learnerSeed hlaunch hbefore).rewards = rewards := rfl

theorem sourceInitializedLaunchSuccessorInput_coordinator (p : Parameters)
    (rate : RateInput p) (source : SourceInput p) (rewards : GridRewardTable p)
    (C_star C_h : ℝ) (launch : BootstrapCoordinatorLocalRound.LaunchedBlock p)
    (learnerSeed : ActualInitializationRun.CoordinatorLearnerZeroSeed p)
    (hlaunch : (ActualInitializationHorizon.sourceInitializedRun p rate source rewards
      C_star C_h).terminalDisposition = .launched launch learnerSeed)
    (hbefore : launch.monitor.launchPosition < p.T) :
    (sourceInitializedLaunchSuccessorInput p rate source rewards C_star C_h
      launch learnerSeed hlaunch hbefore).state.coordinator = .first := rfl

theorem sourceInitializedLaunchSuccessorInput_bank (p : Parameters)
    (rate : RateInput p) (source : SourceInput p) (rewards : GridRewardTable p)
    (C_star C_h : ℝ) (launch : BootstrapCoordinatorLocalRound.LaunchedBlock p)
    (learnerSeed : ActualInitializationRun.CoordinatorLearnerZeroSeed p)
    (hlaunch : (ActualInitializationHorizon.sourceInitializedRun p rate source rewards
      C_star C_h).terminalDisposition = .launched launch learnerSeed)
    (hbefore : launch.monitor.launchPosition < p.T) :
    (sourceInitializedLaunchSuccessorInput p rate source rewards C_star C_h
      launch learnerSeed hlaunch hbefore).state.upDecoderBank =
        CoordinatorUpReception.initialUpDecoderBank p := rfl

theorem sourceInitializedLaunchSuccessorInput_time_val (p : Parameters)
    (rate : RateInput p) (source : SourceInput p) (rewards : GridRewardTable p)
    (C_star C_h : ℝ) (launch : BootstrapCoordinatorLocalRound.LaunchedBlock p)
    (learnerSeed : ActualInitializationRun.CoordinatorLearnerZeroSeed p)
    (hlaunch : (ActualInitializationHorizon.sourceInitializedRun p rate source rewards
      C_star C_h).terminalDisposition = .launched launch learnerSeed)
    (hbefore : launch.monitor.launchPosition < p.T) :
    (sourceInitializedLaunchSuccessorInput p rate source rewards C_star C_h
      launch learnerSeed hlaunch hbefore).time.val = launch.monitor.launchPosition := by
  let run := ActualInitializationHorizon.sourceInitializedRun p rate source rewards C_star C_h
  let next := sourceInitializedLaunchSuccessorBlock p rate source rewards C_star C_h
    launch learnerSeed hlaunch hbefore
  let input := sourceInitializedLaunchSuccessorInput p rate source rewards C_star C_h
    launch learnerSeed hlaunch hbefore
  have hstrict := ActualInitializationHorizon.sourceInitializedRun_terminal_launch_strict
    p rate source rewards C_star C_h launch learnerSeed hlaunch
  have hsuccessor := sourceInitializedRun_launch_has_successor p rate source rewards
    C_star C_h launch learnerSeed hlaunch hbefore
  have hblockStart : BootstrapObservedFollower.blockStart p next =
      (run.terminalBlock.val + 1) * B_boot p := by
    change BootstrapObservedFollower.blockStart p
      (ActualInitializationRun.successorBlock p run.terminalBlock hsuccessor) = _
    simp [ActualInitializationRun.successorBlock, BootstrapObservedFollower.blockStart]
  have hstart : BootstrapObservedFollower.blockStart p next =
      BootstrapObservedFollower.blockStop p run.terminalBlock := by
    have hactivation := BootstrapObservedFollower.nextActivationRound_nonlast_eq_nextStart
      p run.terminalBlock hsuccessor
    change BootstrapObservedFollower.blockStop p run.terminalBlock + 1 =
      (run.terminalBlock.val + 1) * B_boot p + 1 at hactivation
    rw [← hblockStart] at hactivation
    omega
  calc
    input.time.val = BootstrapObservedFollower.blockStart p next := by
      change (ActualInitializationRun.blockTime p next 0 input.cursor_lt).val = _
      simp [ActualInitializationRun.blockTime]
    _ = BootstrapObservedFollower.blockStop p run.terminalBlock := hstart
    _ = launch.monitor.launchPosition := hstrict.2.2.2.symm

/-- The launch learner seed retained by H is exactly its zero-valued source
seed; it is carried into the adapter as evidence, not reinitialized here. -/
theorem sourceInitializedLaunchSuccessor_seed_zero (p : Parameters)
    (learnerSeed : ActualInitializationRun.CoordinatorLearnerZeroSeed p) :
    (∀ arm, learnerSeed.baseScores arm = 0) ∧
      (∀ arm, learnerSeed.queues arm = 0) := by
  exact ⟨learnerSeed.baseScores_zero, learnerSeed.queues_zero⟩

/-- A launch at the clipped final boundary is at `T` and has no successor
physical round. This is separate from the exhausted, never-launched case. -/
theorem sourceInitializedRun_finalLaunch_no_successor_round (p : Parameters)
    (rate : RateInput p) (source : SourceInput p) (rewards : GridRewardTable p)
    (C_star C_h : ℝ) (launch : BootstrapCoordinatorLocalRound.LaunchedBlock p)
    (learnerSeed : ActualInitializationRun.CoordinatorLearnerZeroSeed p)
    (hlast : (ActualInitializationHorizon.sourceInitializedRun p rate source rewards
      C_star C_h).terminalBlock.val + 1 = n_boot p)
    (hlaunch : (ActualInitializationHorizon.sourceInitializedRun p rate source rewards
      C_star C_h).terminalDisposition = .launched launch learnerSeed) :
    launch.monitor.launchPosition = p.T ∧ ¬ launch.monitor.launchPosition < p.T := by
  have hfinal := ActualInitializationHorizon.sourceInitializedRun_final_launch_round
    p rate source rewards C_star C_h launch learnerSeed hlast hlaunch
  have hposition := hfinal.2
  omega

/-- An exhausted terminal boundary has no launch object, so it cannot enter
the launched-successor adapter. -/
theorem sourceInitializedRun_exhausted_not_launched (p : Parameters)
    (rate : RateInput p) (source : SourceInput p) (rewards : GridRewardTable p)
    (C_star C_h : ℝ) (live : BootstrapCoordinatorLocalRound.PrelaunchBlock p)
    (hexhausted : (ActualInitializationHorizon.sourceInitializedRun p rate source rewards
      C_star C_h).terminalDisposition = .exhausted live)
    (launch : BootstrapCoordinatorLocalRound.LaunchedBlock p)
    (learnerSeed : ActualInitializationRun.CoordinatorLearnerZeroSeed p) :
    (ActualInitializationHorizon.sourceInitializedRun p rate source rewards
      C_star C_h).terminalDisposition ≠ .launched launch learnerSeed := by
  intro h
  rw [hexhausted] at h
  cases h

end Bandits.Support.ActualPostlaunchPhysicalStep

end
