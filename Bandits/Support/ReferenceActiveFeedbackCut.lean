/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.DeclaredFollowerLocalRound
public import Bandits.Support.CompletePublicTable
public import Bandits.Support.FiniteBanditModel
public import Bandits.Support.ActualInitializationPhysicalStep

/-!
# Direct follower preparation and finite feedback cut

The local follower operation order and dagger fallback are specified in
`sources/zip4/manuscript/06_interruptions.tex:235-297` and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:6-14`. The active
assignment row, follower assignments, and full-table input are specified in
`sources/zip4/manuscript/05_binary_transport.tex:60-124`. The simultaneous
collision rule and local observation ranges follow the accepted finite model
and the checked local protocol in the cited passages.

This module computes each declared follower's accepted PREPARE result from its
own carried activation and configuration on the selected complete row. Its
reusable action interface receives the coordinator arm as an explicit internal
input supplied by the external dispatcher. It does not construct a coordinator
clock transition, call an observer, filter a message, establish a physical
history or reward law, or close a manuscript theorem.
-/

@[expose] public section

noncomputable section

local instance propDecidable (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition

open Bandits.Support.ConstructorDimensions
open Bandits.Support.CompletePublicTable
open Bandits.Support.ReferencePrelaunchFollower
open Bandits.Support.ActiveFollowerLifecycle
open Bandits.Support.ActiveFollowerQueueOperation
open Bandits.Support.ActiveFollowerArmChoice
open Bandits.Support.OrdinaryMessageCodec
open Bandits.Support.ActiveRoundActions
open Bandits.Support.PublicDiscreteDraws

namespace Bandits.Support.ReferenceActiveFeedbackCut

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := Bandits.Support.ActiveFollowerDownAcceptance.RateInput

/-- The complete public row table, one fixed true row coordinate, the
calendar round, and each declared follower's own original local inputs. -/
structure RoundInput (p : Parameters) (rate : RateInput p) where
  rows : CompletePublicTable.CompleteRows p
  selected : Fin (M p)
  time : Fin p.T
  activations : Fin (p.m - 1) → ReferencePrelaunchFollower.Activation p
  active : ∀ i, (activations i).val ≤ time.val + 1
  configurations : Fin (p.m - 1) → DeclaredFollowerLocalRound.LocalConfiguration p rate

/-- The complete row selected from the retained full table. -/
def RoundInput.selectedRow {p : Parameters} {rate : RateInput p}
    (input : RoundInput p rate) : CompletePublicTable.CompleteRow p :=
  input.rows input.selected

/-- Compute every follower's own accepted PREPARE exactly once from that
follower's own activation, active-time proof, and carried configuration. -/
noncomputable def prepareFollowers {p : Parameters} {rate : RateInput p}
    (input : RoundInput p rate) :
    Fin (p.m - 1) → DeclaredFollowerLocalRound.PreparedRound p rate :=
  fun i => DeclaredFollowerLocalRound.prepare rate i (input.rows input.selected)
    (input.activations i) input.time (input.active i) (input.configurations i)

/-- Each retained follower snapshot is the actual local PREPARE result on the
original selected complete row and that follower's original local inputs. -/
theorem prepareFollowers_apply {p : Parameters} {rate : RateInput p}
    (input : RoundInput p rate) (i : Fin (p.m - 1)) :
    prepareFollowers input i =
      DeclaredFollowerLocalRound.prepare rate i (input.rows input.selected)
        (input.activations i) input.time (input.active i) (input.configurations i) := rfl

/-- The full collection of independently prepared declared-follower
snapshots, with every result tied to its literal accepted PREPARE call. -/
structure PreparedRound {p : Parameters} {rate : RateInput p}
    (input : RoundInput p rate) where
  followers : Fin (p.m - 1) → DeclaredFollowerLocalRound.PreparedRound p rate
  followers_eq : ∀ i, followers i = prepareFollowers input i

/-- Retain all follower preparations before any reward or feedback is
available. -/
noncomputable def prepare {p : Parameters} {rate : RateInput p}
    (input : RoundInput p rate) : PreparedRound input :=
  { followers := prepareFollowers input
    followers_eq := fun _ => rfl }

/-- Reusable physical action inputs. `coordinatorArm` is an explicit internal
arm supplied by the external dispatcher; the follower component is the
retained result of `prepare` above. -/
structure ActionInputs {p : Parameters} {rate : RateInput p}
    (input : RoundInput p rate) where
  coordinatorArm : Fin p.K
  preparation : PreparedRound input

namespace ActionInputs

variable {p : Parameters} {rate : RateInput p} {input : RoundInput p rate}

/-- The simultaneous player-to-arm profile from the supplied coordinator arm
and each follower's retained own prepared arm. -/
def actions (inputs : ActionInputs input) :
    FiniteBanditModel.ActionProfile p.m p.K := fun player =>
  if hplayer : player = ActiveRoundActions.coordinator p.two_le_m then
    inputs.coordinatorArm
  else
    (inputs.preparation.followers
      (ActiveRoundActions.followerIndex p.two_le_m player hplayer)).arm

/-- The coordinator component is the explicit dispatcher-supplied input. -/
theorem actions_coordinator (inputs : ActionInputs input) :
    inputs.actions (ActiveRoundActions.coordinator p.two_le_m) = inputs.coordinatorArm := by
  simp [actions]

/-- Each follower component is the arm from its retained PREPARE result. -/
theorem actions_follower (inputs : ActionInputs input)
    (i : Fin (p.m - 1)) :
    inputs.actions (PublicDiscreteDraws.followerPlayer p.two_le_m i) =
      (inputs.preparation.followers i).arm := by
  unfold actions
  rw [dite_eq_right (ActiveRoundActions.followerPlayer_ne_coordinator p.two_le_m i)]
  rw [ActiveRoundActions.followerIndex_followerPlayer p.two_le_m i
    (ActiveRoundActions.followerPlayer_ne_coordinator p.two_le_m i)]

/-- The follower action is exactly its single accepted PREPARE arm on its own
original local inputs. -/
theorem actions_follower_eq_prepare (inputs : ActionInputs input)
    (i : Fin (p.m - 1)) :
    inputs.actions (PublicDiscreteDraws.followerPlayer p.two_le_m i) =
      (DeclaredFollowerLocalRound.prepare rate i (input.rows input.selected)
        (input.activations i) input.time (input.active i) (input.configurations i)).arm := by
  rw [inputs.actions_follower, inputs.preparation.followers_eq i]
  rw [prepareFollowers_apply]

/-- A prior local dagger plays its prescribed source-index fallback arm. -/
theorem actions_follower_dagger (inputs : ActionInputs input)
    (i : Fin (p.m - 1))
    (hdagger : input.configurations i = .dagger) :
    inputs.actions (PublicDiscreteDraws.followerPlayer p.two_le_m i) =
      DeclaredFollowerLocalRound.fallbackArm p i := by
  rw [inputs.actions_follower_eq_prepare, hdagger]
  exact (DeclaredFollowerLocalRound.prepare_dagger rate i
    (input.rows input.selected) (input.activations i) input.time (input.active i)).1

/-- A failed local start check enters dagger and uses the prescribed fallback
before any offer or arm-choice operation. -/
theorem actions_follower_start_failure (inputs : ActionInputs input)
    (i : Fin (p.m - 1))
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hconfiguration : input.configurations i = .ordinary state memory)
    (reason : ActiveFollowerLifecycle.LifecycleFailure)
    (hstart : ActiveFollowerLifecycle.startRound rate.eta input.time state memory =
      .error reason) :
    inputs.actions (PublicDiscreteDraws.followerPlayer p.two_le_m i) =
      DeclaredFollowerLocalRound.fallbackArm p i := by
  rw [inputs.actions_follower_eq_prepare, hconfiguration]
  exact (DeclaredFollowerLocalRound.prepare_start_failure rate i
    (input.rows input.selected) (input.activations i) input.time (input.active i)
    state memory reason hstart).1

/-- A failed checked UP offer enters dagger and uses the prescribed fallback
before arm choice. -/
theorem actions_follower_offer_failure (inputs : ActionInputs input)
    (i : Fin (p.m - 1))
    (state choiceState : ReferencePrelaunchFollower.State p rate.eta)
    (memory choiceMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hconfiguration : input.configurations i = .ordinary state memory)
    (hstart : ActiveFollowerLifecycle.startRound rate.eta input.time state memory =
      .ok (choiceState, choiceMemory))
    (hoff : ActiveFollowerQueueOperation.checkedUpOffer rate.eta i
      (input.rows input.selected) (input.activations i) input.time choiceState = .failure) :
    inputs.actions (PublicDiscreteDraws.followerPlayer p.two_le_m i) =
      DeclaredFollowerLocalRound.fallbackArm p i := by
  rw [inputs.actions_follower_eq_prepare, hconfiguration]
  exact (DeclaredFollowerLocalRound.prepare_offer_failure rate i
    (input.rows input.selected) (input.activations i) input.time (input.active i)
    state choiceState memory choiceMemory hstart hoff).1

/-- A rejected no-offer local arm choice enters dagger and uses the prescribed
fallback. -/
theorem actions_follower_no_offer_choice_failure (inputs : ActionInputs input)
    (i : Fin (p.m - 1))
    (state choiceState : ReferencePrelaunchFollower.State p rate.eta)
    (memory choiceMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hconfiguration : input.configurations i = .ordinary state memory)
    (hstart : ActiveFollowerLifecycle.startRound rate.eta input.time state memory =
      .ok (choiceState, choiceMemory))
    (hoff : ActiveFollowerQueueOperation.checkedUpOffer rate.eta i
      (input.rows input.selected) (input.activations i) input.time choiceState = .noOffer)
    (hchoice : ActiveFollowerArmChoice.followerArmChoice choiceState
      (input.rows input.selected) input.time i none = none) :
    inputs.actions (PublicDiscreteDraws.followerPlayer p.two_le_m i) =
      DeclaredFollowerLocalRound.fallbackArm p i := by
  rw [inputs.actions_follower_eq_prepare, hconfiguration]
  exact ((DeclaredFollowerLocalRound.prepare_no_offer_arm_equation rate i
    (input.rows input.selected) (input.activations i) input.time (input.active i)
    state choiceState memory choiceMemory hstart hoff).1 hchoice).1

/-- A rejected offer-based local arm choice enters dagger and uses the
prescribed fallback. -/
theorem actions_follower_offer_choice_failure (inputs : ActionInputs input)
    (i : Fin (p.m - 1))
    (state choiceState : ReferencePrelaunchFollower.State p rate.eta)
    (memory choiceMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hconfiguration : input.configurations i = .ordinary state memory)
    (offered : OrdinaryMessageCodec.UpRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta))
    (hstart : ActiveFollowerLifecycle.startRound rate.eta input.time state memory =
      .ok (choiceState, choiceMemory))
    (hoff : ActiveFollowerQueueOperation.checkedUpOffer rate.eta i
      (input.rows input.selected) (input.activations i) input.time choiceState =
        .offer offered)
    (hchoice : ActiveFollowerArmChoice.followerArmChoice choiceState
      (input.rows input.selected) input.time i (some offered) = none) :
    inputs.actions (PublicDiscreteDraws.followerPlayer p.two_le_m i) =
      DeclaredFollowerLocalRound.fallbackArm p i := by
  rw [inputs.actions_follower_eq_prepare, hconfiguration]
  exact ((DeclaredFollowerLocalRound.prepare_offer_arm_equation rate i
    (input.rows input.selected) (input.activations i) input.time (input.active i)
    state choiceState memory choiceMemory hstart offered hoff).1 hchoice).1

/-- A successful no-offer local arm choice is used verbatim. -/
theorem actions_follower_no_offer_choice (inputs : ActionInputs input)
    (i : Fin (p.m - 1))
    (state choiceState : ReferencePrelaunchFollower.State p rate.eta)
    (memory choiceMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hconfiguration : input.configurations i = .ordinary state memory)
    (arm : Fin p.K)
    (hstart : ActiveFollowerLifecycle.startRound rate.eta input.time state memory =
      .ok (choiceState, choiceMemory))
    (hoff : ActiveFollowerQueueOperation.checkedUpOffer rate.eta i
      (input.rows input.selected) (input.activations i) input.time choiceState = .noOffer)
    (hchoice : ActiveFollowerArmChoice.followerArmChoice choiceState
      (input.rows input.selected) input.time i none = some arm) :
    inputs.actions (PublicDiscreteDraws.followerPlayer p.two_le_m i) = arm := by
  rw [inputs.actions_follower_eq_prepare, hconfiguration]
  exact ((DeclaredFollowerLocalRound.prepare_no_offer_arm_equation rate i
    (input.rows input.selected) (input.activations i) input.time (input.active i)
    state choiceState memory choiceMemory hstart hoff).2 arm hchoice).1

/-- A successful checked offer is passed unchanged to local arm choice. -/
theorem actions_follower_offer_choice (inputs : ActionInputs input)
    (i : Fin (p.m - 1))
    (state choiceState : ReferencePrelaunchFollower.State p rate.eta)
    (memory choiceMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hconfiguration : input.configurations i = .ordinary state memory)
    (offered : OrdinaryMessageCodec.UpRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta))
    (arm : Fin p.K)
    (hstart : ActiveFollowerLifecycle.startRound rate.eta input.time state memory =
      .ok (choiceState, choiceMemory))
    (hoff : ActiveFollowerQueueOperation.checkedUpOffer rate.eta i
      (input.rows input.selected) (input.activations i) input.time choiceState =
        .offer offered)
    (hchoice : ActiveFollowerArmChoice.followerArmChoice choiceState
      (input.rows input.selected) input.time i (some offered) = some arm) :
    inputs.actions (PublicDiscreteDraws.followerPlayer p.two_le_m i) = arm := by
  rw [inputs.actions_follower_eq_prepare, hconfiguration]
  exact ((DeclaredFollowerLocalRound.prepare_offer_arm_equation rate i
    (input.rows input.selected) (input.activations i) input.time (input.active i)
    state choiceState memory choiceMemory hstart offered hoff).2 arm hchoice).1

end ActionInputs

/-- The finite collision-feedback grid on a fixed action profile and reward
slice. -/
noncomputable def collisionFeedbackVector {p : Parameters}
    (actions : FiniteBanditModel.ActionProfile p.m p.K) (time : Fin p.T)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) :
    Fin p.m → Fin (D p + 1) := by
  classical
  exact fun player =>
    if FiniteBanditModel.collisionFreeFor actions player then
      rewards time (actions player) else 0

/-- The literal coordinate equation for the finite collision-feedback grid. -/
theorem collisionFeedbackVector_apply {p : Parameters}
    (actions : FiniteBanditModel.ActionProfile p.m p.K) (time : Fin p.T)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (player : Fin p.m) :
    collisionFeedbackVector actions time rewards player =
      if FiniteBanditModel.collisionFreeFor actions player then
        rewards time (actions player) else 0 := by
  classical
  rfl

/-- One direct deterministic feedback cut. Its own entries and observations
are derived from the same stored finite feedback vector and action profile. -/
structure FeedbackCut {p : Parameters} {rate : RateInput p}
    {input : RoundInput p rate} (arms : ActionInputs input)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) where
  armInputs : ActionInputs input
  armInputs_eq : armInputs = arms
  feedback : Fin p.m → Fin (D p + 1)
  feedback_eq : feedback = collisionFeedbackVector armInputs.actions input.time rewards
  observations : Fin p.m → ReferencePrelaunchFollower.Observation p
  observations_eq : ∀ player, observations player =
    ActualInitializationPhysicalStep.observationOfGrid p (feedback player)
  ownEntries : Fin p.m → Fin p.K × ReferencePrelaunchFollower.Observation p
  ownEntries_eq : ∀ player, ownEntries player =
    (armInputs.actions player, observations player)

/-- The one action profile retained by this direct feedback cut. -/
def FeedbackCut.actions {p : Parameters} {rate : RateInput p}
    {input : RoundInput p rate} {arms : ActionInputs input}
    {rewards : ActualInitializationPhysicalStep.GridRewardTable p}
    (cut : FeedbackCut arms rewards) : FiniteBanditModel.ActionProfile p.m p.K :=
  cut.armInputs.actions

/-- Assemble the finite collision vector, typed observations, and exact own
entries after actions are fixed. No local observation transition is run. -/
def assembleFeedback {p : Parameters} {rate : RateInput p}
    {input : RoundInput p rate} (arms : ActionInputs input)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) :
    FeedbackCut arms rewards := by
  classical
  let feedback := collisionFeedbackVector arms.actions input.time rewards
  let observations : Fin p.m → ReferencePrelaunchFollower.Observation p :=
    fun player => ActualInitializationPhysicalStep.observationOfGrid p (feedback player)
  exact
    { armInputs := arms
      armInputs_eq := rfl
      feedback := feedback
      feedback_eq := rfl
      observations := observations
      observations_eq := by intro player; rfl
      ownEntries := fun player => (arms.actions player, observations player)
      ownEntries_eq := by intro player; rfl }

namespace FeedbackCut

variable {p : Parameters} {rate : RateInput p}
  {input : RoundInput p rate} {arms : ActionInputs input}
  {rewards : ActualInitializationPhysicalStep.GridRewardTable p}

/-- The assembled coordinator action is exactly the explicit internal input. -/
theorem actions_coordinator (cut : FeedbackCut arms rewards) :
    cut.actions (ActiveRoundActions.coordinator p.two_le_m) = arms.coordinatorArm := by
  change cut.armInputs.actions (ActiveRoundActions.coordinator p.two_le_m) =
    arms.coordinatorArm
  rw [cut.armInputs_eq]
  exact arms.actions_coordinator

/-- Each assembled follower action is exactly its retained own prepared arm. -/
theorem actions_follower (cut : FeedbackCut arms rewards)
    (i : Fin (p.m - 1)) :
    cut.actions (PublicDiscreteDraws.followerPlayer p.two_le_m i) =
      (arms.preparation.followers i).arm := by
  change cut.armInputs.actions (PublicDiscreteDraws.followerPlayer p.two_le_m i) =
    (arms.preparation.followers i).arm
  rw [cut.armInputs_eq]
  exact arms.actions_follower i

/-- The stored grid entry is precisely the finite collision rule on this same
action profile and selected calendar coordinate. -/
theorem feedback_collision_rule (cut : FeedbackCut arms rewards)
    (player : Fin p.m) :
    cut.feedback player =
      if FiniteBanditModel.collisionFreeFor cut.actions player then
        rewards input.time (cut.actions player) else 0 := by
  rw [cut.feedback_eq]
  exact collisionFeedbackVector_apply cut.actions input.time rewards player

/-- The real value of the stored grid entry is the finite-bandit scalar
feedback model on the same action profile and reward slice. -/
theorem feedback_scalar_eq_playerFeedback (cut : FeedbackCut arms rewards)
    (player : Fin p.m) :
    ((cut.feedback player).val : ℝ) / (D p : ℝ) =
      FiniteBanditModel.playerFeedback cut.actions
        (fun arm => ((rewards input.time arm).val : ℝ) / (D p : ℝ)) player := by
  classical
  change ((cut.feedback player).val : ℝ) / (D p : ℝ) =
    FiniteBanditModel.playerFeedback cut.armInputs.actions
      (fun arm => ((rewards input.time arm).val : ℝ) / (D p : ℝ)) player
  rw [cut.feedback_eq]
  rw [collisionFeedbackVector_apply]
  by_cases hfree : FiniteBanditModel.collisionFreeFor cut.armInputs.actions player
  · simp [FiniteBanditModel.playerFeedback, hfree]
  · simp [FiniteBanditModel.playerFeedback, hfree]

/-- Each typed observation is the accepted quantization of the same stored
finite-grid feedback coordinate. -/
theorem observation_grid_value (cut : FeedbackCut arms rewards)
    (player : Fin p.m) :
    (cut.observations player).val.val =
      ((cut.feedback player).val : ℝ) / (D p : ℝ) := by
  rw [cut.observations_eq]
  exact ActualInitializationPhysicalStep.observationOfGrid_value p
    (cut.feedback player)

/-- Every typed observation lies in the accepted local scalar interval. -/
theorem observation_bounds (cut : FeedbackCut arms rewards)
    (player : Fin p.m) :
    (cut.observations player).val.val ∈ Set.Icc (0 : ℝ) 1 :=
  (cut.observations player).val.property

/-- The exact own entry uses this player's action and the observation made from
the same single feedback vector. -/
theorem own_entry_eq (cut : FeedbackCut arms rewards)
    (player : Fin p.m) :
    cut.ownEntries player =
      (cut.actions player,
        ActualInitializationPhysicalStep.observationOfGrid p (cut.feedback player)) := by
  change cut.ownEntries player =
    (cut.armInputs.actions player,
      ActualInitializationPhysicalStep.observationOfGrid p (cut.feedback player))
  rw [cut.ownEntries_eq, cut.observations_eq]

end FeedbackCut

end Bandits.Support.ReferenceActiveFeedbackCut

end
