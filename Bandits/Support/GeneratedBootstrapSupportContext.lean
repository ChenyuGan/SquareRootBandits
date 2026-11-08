/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.BootstrapPhysicalBlock
public import Bandits.Support.BootstrapPhysicalInput
public import Bandits.Support.CompletePublicTable
public import Bandits.Support.FalseForwardContextBound
public import Bandits.Support.ReferenceInitializationRun

/-!
# Actual two-player support context for a physical bootstrap block

This module gives the deterministic current-block reduction used by
`appendix_b_communication.tex:302-326,350-365` and
`07_public_setup.tex:27-38,75-113,123-140` in the pinned manuscript.  Its
context map is defined only for a local follower in a processed boundary of
the actual `ReferenceInitializationRun`; the physical input is the accepted
`BootstrapPhysicalInput.blockInput`, and its state is the existing
`BootstrapPhysicalBlock.run` state.

The support vectors record rounded reward support and the actual simultaneous
actions of every peer other than the coordinator and the tested follower.
They determine the coordinator's DISCOVER tests and the tested follower's
ID-zero feedback tests on every slot.  They do not determine a whole reference
boundary, numerical observations, DOWN counters, launch, or block completion.
The comparison below keeps the full all-slot gain, including slots after a
pending declaration has been saved and the first block that may launch at its
boundary.  Candidate eligibility must still intersect ID-zero positivity with
that candidate's own DATA slot.

This is an internal deterministic reduction only.  It makes no conditional
law, generated-boundary measurability, false-forward tail, or manuscript
closure claim.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.FiniteBanditModel
open Bandits.Support.PublicDiscreteDraws
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.BootstrapPhysicalBlock
open Bandits.Support.BootstrapPhysicalInput
open Bandits.Support.ReferenceInitializationRun
open Bandits.Support.CompletePublicTable
open Bandits.Support.FalseRowSliceFactorization
open scoped Classical

namespace Bandits.Support.GeneratedBootstrapSupportContext

variable {p : Parameters} {s : Fin (n_boot p)}

/-- The support and peer-avoidance condition at one actual pre-choice state.
The actions are read from the existing simultaneous physical profile. -/
def supportAvoidanceAt (v : BootstrapPhysicalBlock.Input p s)
    (j : {j // j ∈ v.uninformed}) (c : Fin p.K)
    (st : BootstrapPhysicalBlock.State p) (t : Fin p.T) : Bool := by
  classical
  exact decide
    (0 < (v.rewards t c).val ∧
      ∀ k : Fin p.m,
        k ≠ ActiveRoundActions.coordinator p.two_le_m →
        k ≠ PublicDiscreteDraws.followerPlayer p.two_le_m j.1 →
        BootstrapPhysicalBlock.actions v st t k ≠ c)

/-- The literal source support vector on the actual finite block time subtype.
At each slot it evaluates the EXISTING run state and physical action profile. -/
def supportAvoidanceVector (v : BootstrapPhysicalBlock.Input p s)
    (j : {j // j ∈ v.uninformed}) (c : Fin p.K) :
    BlockTime p s → Bool := fun t =>
  supportAvoidanceAt v j c (BootstrapPhysicalBlock.run v t.1) t.1

theorem actions_eq_of_not_coordinator (v : BootstrapPhysicalBlock.Input p s)
    (st₁ st₂ : BootstrapPhysicalBlock.State p) (t : Fin p.T)
    (k : Fin p.m) (hk : k ≠ ActiveRoundActions.coordinator p.two_le_m) :
    BootstrapPhysicalBlock.actions v st₁ t k =
      BootstrapPhysicalBlock.actions v st₂ t k := by
  simp only [BootstrapPhysicalBlock.actions, dite_eq_right hk]

/-- Peer choices have no pre-choice dependence on DISCOVER state. -/
theorem supportAvoidanceAt_eq_of_state (v : BootstrapPhysicalBlock.Input p s)
    (j : {j // j ∈ v.uninformed}) (c : Fin p.K)
    (st₁ st₂ : BootstrapPhysicalBlock.State p) (t : Fin p.T) :
    supportAvoidanceAt v j c st₁ t = supportAvoidanceAt v j c st₂ t := by
  classical
  have hiff :
      (0 < (v.rewards t c).val ∧
        ∀ k : Fin p.m,
          k ≠ ActiveRoundActions.coordinator p.two_le_m →
          k ≠ PublicDiscreteDraws.followerPlayer p.two_le_m j.1 →
          BootstrapPhysicalBlock.actions v st₁ t k ≠ c) ↔
      (0 < (v.rewards t c).val ∧
        ∀ k : Fin p.m,
          k ≠ ActiveRoundActions.coordinator p.two_le_m →
          k ≠ PublicDiscreteDraws.followerPlayer p.two_le_m j.1 →
          BootstrapPhysicalBlock.actions v st₂ t k ≠ c) := by
    constructor
    · rintro ⟨hr, hp⟩
      refine ⟨hr, ?_⟩
      intro k hk₀ hkj
      rw [← actions_eq_of_not_coordinator v st₁ st₂ t k hk₀]
      exact hp k hk₀ hkj
    · rintro ⟨hr, hp⟩
      refine ⟨hr, ?_⟩
      intro k hk₀ hkj
      rw [actions_eq_of_not_coordinator v st₁ st₂ t k hk₀]
      exact hp k hk₀ hkj
  exact Bool.decide_congr hiff

theorem supportAvoidanceVector_eq_at_state
    (v : BootstrapPhysicalBlock.Input p s)
    (j : {j // j ∈ v.uninformed}) (c : Fin p.K)
    (st : BootstrapPhysicalBlock.State p) (t : BlockTime p s) :
    supportAvoidanceVector v j c t = supportAvoidanceAt v j c st t.1 := by
  exact supportAvoidanceAt_eq_of_state v j c
    (BootstrapPhysicalBlock.run v t.1) st t.1

theorem supportAvoidanceAt_true_iff (v : BootstrapPhysicalBlock.Input p s)
    (j : {j // j ∈ v.uninformed}) (c : Fin p.K)
    (st : BootstrapPhysicalBlock.State p) (t : Fin p.T) :
    supportAvoidanceAt v j c st t = true ↔
      0 < (v.rewards t c).val ∧
        ∀ k : Fin p.m,
          k ≠ ActiveRoundActions.coordinator p.two_le_m →
          k ≠ PublicDiscreteDraws.followerPlayer p.two_le_m j.1 →
          BootstrapPhysicalBlock.actions v st t k ≠ c := by
  simp [supportAvoidanceAt]

theorem supportAvoidanceVector_true_iff
    (v : BootstrapPhysicalBlock.Input p s)
    (j : {j // j ∈ v.uninformed}) (c : Fin p.K) (t : BlockTime p s) :
    supportAvoidanceVector v j c t = true ↔
      0 < (v.rewards t.1 c).val ∧
        ∀ k : Fin p.m,
          k ≠ ActiveRoundActions.coordinator p.two_le_m →
          k ≠ PublicDiscreteDraws.followerPlayer p.two_le_m j.1 →
          BootstrapPhysicalBlock.actions v
            (BootstrapPhysicalBlock.run v t.1) t.1 k ≠ c := by
  rw [supportAvoidanceVector_eq_at_state v j c
    (BootstrapPhysicalBlock.run v t.1) t]
  exact supportAvoidanceAt_true_iff v j c _ t.1

private theorem gridIndex_pos_iff (q : Fin (D p + 1)) :
    0 < RealRewardGridCount.realRewardGridValue (D p) (D_pos p) q ↔
      0 < q.val := by
  have hD : (0 : ℝ) < (D p : ℝ) := by exact_mod_cast D_pos p
  rw [RealRewardGridCount.realRewardGridValue, div_pos_iff_of_pos_right hD]
  exact_mod_cast (Iff.rfl : 0 < q.val ↔ 0 < q.val)

private theorem feedback_pos_iff_collision_reward
    (v : BootstrapPhysicalBlock.Input p s)
    (st : BootstrapPhysicalBlock.State p) (t : Fin p.T) (i : Fin p.m) :
    0 < BootstrapPhysicalBlock.feedback v st t i ↔
      FiniteBanditModel.collisionFreeFor
        (BootstrapPhysicalBlock.actions v st t) i ∧
        0 < (v.rewards t
          (BootstrapPhysicalBlock.actions v st t i)).val := by
  classical
  by_cases hfree : FiniteBanditModel.collisionFreeFor
      (BootstrapPhysicalBlock.actions v st t) i
  · simp [BootstrapPhysicalBlock.feedback, FiniteBanditModel.playerFeedback,
      hfree, gridIndex_pos_iff]
  · simp [BootstrapPhysicalBlock.feedback, FiniteBanditModel.playerFeedback,
      hfree]

private theorem collisionFree_coordinator_iff
    (v : BootstrapPhysicalBlock.Input p s)
    (st : BootstrapPhysicalBlock.State p) (t : Fin p.T)
    (j : {j // j ∈ v.uninformed}) (z : Fin p.K)
    (hcoord : BootstrapPhysicalBlock.actions v st t
      (ActiveRoundActions.coordinator p.two_le_m) = z) :
    FiniteBanditModel.collisionFreeFor
        (BootstrapPhysicalBlock.actions v st t)
        (ActiveRoundActions.coordinator p.two_le_m) ↔
      BootstrapPhysicalBlock.actions v st t
          (PublicDiscreteDraws.followerPlayer p.two_le_m j.1) ≠ z ∧
        ∀ k : Fin p.m,
          k ≠ ActiveRoundActions.coordinator p.two_le_m →
          k ≠ PublicDiscreteDraws.followerPlayer p.two_le_m j.1 →
          BootstrapPhysicalBlock.actions v st t k ≠ z := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · simpa [hcoord] using h
        (PublicDiscreteDraws.followerPlayer p.two_le_m j.1)
        (ActiveRoundActions.followerPlayer_ne_coordinator p.two_le_m j.1)
    · intro k hk₀ hkj
      simpa [hcoord] using h k hk₀
  · rintro ⟨hfollower, hpeers⟩ k hk₀
    by_cases hkj : k = PublicDiscreteDraws.followerPlayer p.two_le_m j.1
    · subst k
      simpa [hcoord] using hfollower
    · simpa [hcoord] using hpeers k hk₀ hkj

private theorem collisionFree_follower_iff
    (v : BootstrapPhysicalBlock.Input p s)
    (st : BootstrapPhysicalBlock.State p) (t : Fin p.T)
    (j : {j // j ∈ v.uninformed}) (a : Fin p.K)
    (hfollower : BootstrapPhysicalBlock.actions v st t
      (PublicDiscreteDraws.followerPlayer p.two_le_m j.1) = a) :
    FiniteBanditModel.collisionFreeFor
        (BootstrapPhysicalBlock.actions v st t)
        (PublicDiscreteDraws.followerPlayer p.two_le_m j.1) ↔
      BootstrapPhysicalBlock.actions v st t
          (ActiveRoundActions.coordinator p.two_le_m) ≠ a ∧
        ∀ k : Fin p.m,
          k ≠ ActiveRoundActions.coordinator p.two_le_m →
          k ≠ PublicDiscreteDraws.followerPlayer p.two_le_m j.1 →
          BootstrapPhysicalBlock.actions v st t k ≠ a := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · simpa [hfollower] using h
        (ActiveRoundActions.coordinator p.two_le_m)
        (ActiveRoundActions.followerPlayer_ne_coordinator p.two_le_m j.1).symm
    · intro k hk₀ hkj
      simpa [hfollower] using h k hkj
  · rintro ⟨hcoord, hpeers⟩ k hki
    by_cases hk₀ : k = ActiveRoundActions.coordinator p.two_le_m
    · subst k
      simpa [hfollower] using hcoord
    · simpa [hfollower] using hpeers k hk₀ hki

/-- In true-row DATA while in DISCOVER, coordinator positivity is derived
from the physical collision rule and rounded reward grid. -/
theorem coordinator_feedback_pos_iff_support
    (v : BootstrapPhysicalBlock.Input p s)
    (st : BootstrapPhysicalBlock.State p)
    (j : {j // j ∈ v.uninformed}) (t : BlockTime p s)
    (hm : st.mode = BootstrapPhysicalBlock.Mode.discover)
    (hdata : BootstrapPhysicalBlock.slot v t.1 = PublicDiscreteDraws.dataSlot) :
    0 < BootstrapPhysicalBlock.feedback v st t.1
        (ActiveRoundActions.coordinator p.two_le_m) ↔
      supportAvoidanceVector v j v.target t = true ∧
        BootstrapPhysicalBlock.actions v st t.1
          (PublicDiscreteDraws.followerPlayer p.two_le_m j.1) ≠ v.target := by
  have hcoord : BootstrapPhysicalBlock.actions v st t.1
      (ActiveRoundActions.coordinator p.two_le_m) = v.target := by
    rw [BootstrapPhysicalBlock.actions_coordinator]
    exact BootstrapPhysicalBlock.coordinatorAction_discover_data v st t.1 hm hdata
  rw [feedback_pos_iff_collision_reward, hcoord]
  rw [collisionFree_coordinator_iff v st t.1 j v.target hcoord]
  rw [supportAvoidanceVector_eq_at_state v j v.target st t]
  rw [supportAvoidanceAt_true_iff]
  constructor
  · rintro ⟨⟨hfollower, hpeers⟩, hreward⟩
    exact ⟨⟨hreward, hpeers⟩, hfollower⟩
  · rintro ⟨⟨hreward, hpeers⟩, hfollower⟩
    exact ⟨⟨hfollower, hpeers⟩, hreward⟩

/-- On every slot, an active held-arm follower with ID bit zero has positive
feedback exactly when its support vector is true and the coordinator avoids
the held arm. -/
theorem follower_feedback_pos_iff_support
    (v : BootstrapPhysicalBlock.Input p s)
    (st : BootstrapPhysicalBlock.State p)
    (j : {j // j ∈ v.uninformed}) (t : BlockTime p s)
    (hactive : v.active j = true)
    (hid : v.ids (v.privateId j) t.1 = false) :
    0 < BootstrapPhysicalBlock.feedback v st t.1
        (PublicDiscreteDraws.followerPlayer p.two_le_m j.1) ↔
      supportAvoidanceVector v j (v.held j) t = true ∧
        BootstrapPhysicalBlock.actions v st t.1
          (ActiveRoundActions.coordinator p.two_le_m) ≠ v.held j := by
  have hfollower : BootstrapPhysicalBlock.actions v st t.1
      (PublicDiscreteDraws.followerPlayer p.two_le_m j.1) = v.held j := by
    rw [BootstrapPhysicalBlock.actions_follower,
      BootstrapPhysicalBlock.followerAction]
    simp only [dite_eq_left j.2]
    exact BootstrapPhysicalBlock.uninformedAction_stay v t.1 j hactive hid
  rw [feedback_pos_iff_collision_reward, hfollower]
  rw [collisionFree_follower_iff v st t.1 j (v.held j) hfollower]
  rw [supportAvoidanceVector_eq_at_state v j (v.held j) st t]
  rw [supportAvoidanceAt_true_iff]
  constructor
  · rintro ⟨⟨hcoord, hpeers⟩, hreward⟩
    exact ⟨⟨hreward, hpeers⟩, hcoord⟩
  · rintro ⟨⟨hreward, hpeers⟩, hcoord⟩
    exact ⟨⟨hcoord, hpeers⟩, hreward⟩

/-- The literal existing physical input for an actual incoming boundary and
its processed block index. -/
def actualPhysicalInput (x : ReferenceInitializationRun.Input p)
    (b : ReferenceInitializationRun.Boundary p) (s : Fin (n_boot p)) :
    BootstrapPhysicalBlock.Input p s :=
  BootstrapPhysicalInput.blockInput p s
    (ReferenceInitializationRun.uninformed b) b.numerators b.weight_ge_one
    x.ids x.row x.rewards x.coordinates

/-- An actual processed local block. Its incoming boundary is a value of the
reference recursion at the start of this block, its follower is genuinely
uninformed there, and the follower is active in the accepted physical input.
The selected published row and ID array are recorded explicitly. -/
structure ActualLocalBlock (P : CompletePublicTable.PublishedOutput p)
    (J : Fin (M p)) (x : ReferenceInitializationRun.Input p)
    (s : Fin (n_boot p)) where
  ids_eq : x.ids = P.1
  row_eq : x.row = P.2 J
  incoming : ReferenceInitializationRun.Boundary p
  incoming_eq_run : incoming = ReferenceInitializationRun.run x s.val
  completed_eq : incoming.completed = s.val
  follower : {j // j ∈ (actualPhysicalInput x incoming s).uninformed}
  follower_incoming : follower.1 ∈ ReferenceInitializationRun.uninformed incoming
  active : (actualPhysicalInput x incoming s).active follower = true

/-- The literal map to the EXISTING source `Context` carrier. Its only domain
is an actual processed, uninformed, active local block. -/
def actualContextMap
    (P : CompletePublicTable.PublishedOutput p) (J : Fin (M p))
    (x : ReferenceInitializationRun.Input p) (s : Fin (n_boot p))
    (q : ActualLocalBlock P J x s) : FalseForwardContextBound.Context p :=
  ⟨s, (J, BootstrapPhysicalInput.sourceFollowerIndex p q.follower.1,
    (actualPhysicalInput x q.incoming s).held q.follower,
    (actualPhysicalInput x q.incoming s).target,
    supportAvoidanceVector (actualPhysicalInput x q.incoming s) q.follower
      ((actualPhysicalInput x q.incoming s).held q.follower),
    supportAvoidanceVector (actualPhysicalInput x q.incoming s) q.follower
      ((actualPhysicalInput x q.incoming s).target))⟩

private theorem slot_eq_of_learningRow_eq
    (v w : BootstrapPhysicalBlock.Input p s)
    (t : BlockTime p s)
    (hrow : v.row.2 t.1 = w.row.2 t.1) :
    BootstrapPhysicalBlock.slot v t.1 = BootstrapPhysicalBlock.slot w t.1 := by
  simp [BootstrapPhysicalBlock.slot, hrow]

private theorem tuple_eq_of_learningRow_eq
    (v w : BootstrapPhysicalBlock.Input p s)
    (t : BlockTime p s)
    (hrow : v.row.2 t.1 = w.row.2 t.1) :
    BootstrapPhysicalBlock.tuple v t.1 = BootstrapPhysicalBlock.tuple w t.1 := by
  simp [BootstrapPhysicalBlock.tuple, hrow]

private theorem forwardProduct_eq_of_reads
    (v w : BootstrapPhysicalBlock.Input p s)
    (st : BootstrapPhysicalBlock.State p) (t : BlockTime p s)
    (hrow : ∀ u : Fin (A_id p), v.row.1 u t.1 = w.row.1 u t.1) :
    BootstrapPhysicalBlock.forwardProduct v st t.1 =
      BootstrapPhysicalBlock.forwardProduct w st t.1 := by
  simp [BootstrapPhysicalBlock.forwardProduct, hrow]

private theorem coordinatorAction_eq_of_local_reads
    (v w : BootstrapPhysicalBlock.Input p s)
    (st : BootstrapPhysicalBlock.State p) (t : BlockTime p s)
    (hrowForward : ∀ u : Fin (A_id p), v.row.1 u t.1 = w.row.1 u t.1)
    (hrowLearning : v.row.2 t.1 = w.row.2 t.1)
    (htarget : v.target = w.target)
    (huniform : v.uniform (ActiveRoundActions.coordinator p.two_le_m) t.1 =
      w.uniform (ActiveRoundActions.coordinator p.two_le_m) t.1)
    (havoid : (v.coordinatorAvoid t.1).val = (w.coordinatorAvoid t.1).val) :
    BootstrapPhysicalBlock.coordinatorAction v st t.1 =
      BootstrapPhysicalBlock.coordinatorAction w st t.1 := by
  have hslot := slot_eq_of_learningRow_eq v w t hrowLearning
  have htuple := tuple_eq_of_learningRow_eq v w t hrowLearning
  have hforwardProduct := forwardProduct_eq_of_reads v w st t hrowForward
  classical
  by_cases hdata : BootstrapPhysicalBlock.slot v t.1 = PublicDiscreteDraws.dataSlot
  · have hdata' : BootstrapPhysicalBlock.slot w t.1 = PublicDiscreteDraws.dataSlot := by
      rw [← hslot]
      exact hdata
    simp only [BootstrapPhysicalBlock.coordinatorAction, hdata, hdata', ↓reduceIte]
    by_cases hm : st.mode = BootstrapPhysicalBlock.Mode.multicast ∧
        BootstrapPhysicalBlock.forwardProduct v st t.1 = 1
    · have hm' : st.mode = BootstrapPhysicalBlock.Mode.multicast ∧
          BootstrapPhysicalBlock.forwardProduct w st t.1 = 1 := by
        rw [← hforwardProduct]
        exact hm
      simp [hm, hm', havoid]
    · have hm' : ¬(st.mode = BootstrapPhysicalBlock.Mode.multicast ∧
          BootstrapPhysicalBlock.forwardProduct w st t.1 = 1) := by
        intro hm'
        apply hm
        rw [hforwardProduct]
        exact hm'
      simp [hm, hm', htarget]
  · by_cases hdown : BootstrapPhysicalBlock.slot v t.1 = PublicDiscreteDraws.downSlot
    · have hdata' : BootstrapPhysicalBlock.slot w t.1 ≠ PublicDiscreteDraws.dataSlot := by
        intro hd
        exact hdata (hslot.symm ▸ hd)
      have hdown' : BootstrapPhysicalBlock.slot w t.1 = PublicDiscreteDraws.downSlot := by
        rw [← hslot]
        exact hdown
      simp [BootstrapPhysicalBlock.coordinatorAction, hdown, hdown',
        PublicDiscreteDraws.dataSlot, PublicDiscreteDraws.downSlot, htuple]
    · have hdata' : BootstrapPhysicalBlock.slot w t.1 ≠ PublicDiscreteDraws.dataSlot := by
        intro hd
        exact hdata (hslot.symm ▸ hd)
      have hdown' : BootstrapPhysicalBlock.slot w t.1 ≠ PublicDiscreteDraws.downSlot := by
        intro hd
        exact hdown (hslot.symm ▸ hd)
      simp only [BootstrapPhysicalBlock.coordinatorAction, hdata, hdata', hdown, hdown',
        ↓reduceIte]
      exact huniform

private theorem followerActions_eq_of_local_reads
    (v w : BootstrapPhysicalBlock.Input p s)
    (j : {j // j ∈ v.uninformed}) (k : {j // j ∈ w.uninformed})
    (st : BootstrapPhysicalBlock.State p)
    (t : BlockTime p s)
    (hactive : v.active j = true) (hactive' : w.active k = true)
    (hids : v.ids = w.ids)
    (hid : v.privateId j = w.privateId k)
    (hheld : v.held j = w.held k)
    (havoid : (v.followerAvoid j t.1).val = (w.followerAvoid k t.1).val) :
    BootstrapPhysicalBlock.actions v st t.1
        (PublicDiscreteDraws.followerPlayer p.two_le_m j.1) =
      BootstrapPhysicalBlock.actions w st t.1
        (PublicDiscreteDraws.followerPlayer p.two_le_m k.1) := by
  rw [BootstrapPhysicalBlock.actions_follower, BootstrapPhysicalBlock.actions_follower]
  rw [BootstrapPhysicalBlock.followerAction, BootstrapPhysicalBlock.followerAction]
  simp only [dite_eq_left j.2, dite_eq_left k.2]
  have hbit : v.ids (v.privateId j) t.1 = w.ids (w.privateId k) t.1 := by
    rw [hids, hid]
  simp [BootstrapPhysicalBlock.uninformedAction, hactive, hactive', hbit,
    hheld, havoid]

private theorem discoveryPositive_iff_of_local_reads
    (v w : BootstrapPhysicalBlock.Input p s)
    (j : {j // j ∈ v.uninformed}) (k : {j // j ∈ w.uninformed})
    (st : BootstrapPhysicalBlock.State p) (t : BlockTime p s)
    (hactive : v.active j = true) (hactive' : w.active k = true)
    (hids : v.ids = w.ids)
    (hid : v.privateId j = w.privateId k)
    (hheld : v.held j = w.held k)
    (htarget : v.target = w.target)
    (hrowLearning : v.row.2 t.1 = w.row.2 t.1)
    (havoid : (v.followerAvoid j t.1).val = (w.followerAvoid k t.1).val)
    (hSupportTarget : supportAvoidanceVector v j v.target =
      supportAvoidanceVector w k w.target) :
    BootstrapPhysicalBlock.discoveryPositive v st t.1 ↔
      BootstrapPhysicalBlock.discoveryPositive w st t.1 := by
  have hslot := slot_eq_of_learningRow_eq v w t hrowLearning
  have hfollow := followerActions_eq_of_local_reads v w j k st t
    hactive hactive' hids hid hheld havoid
  simp only [BootstrapPhysicalBlock.discoveryPositive, t.2, true_and]
  by_cases hm : st.mode = BootstrapPhysicalBlock.Mode.discover
  · simp only [hm, true_and]
    by_cases hd : BootstrapPhysicalBlock.slot v t.1 = PublicDiscreteDraws.dataSlot
    · have hd' : BootstrapPhysicalBlock.slot w t.1 = PublicDiscreteDraws.dataSlot :=
        hslot.symm ▸ hd
      simp only [hd, hd', true_and]
      rw [coordinator_feedback_pos_iff_support v st j t hm hd]
      rw [coordinator_feedback_pos_iff_support w st k t hm hd']
      rw [congrFun hSupportTarget t]
      have hneq :
          BootstrapPhysicalBlock.actions v st t.1
              (PublicDiscreteDraws.followerPlayer p.two_le_m j.1) ≠ v.target ↔
            BootstrapPhysicalBlock.actions w st t.1
              (PublicDiscreteDraws.followerPlayer p.two_le_m k.1) ≠ w.target := by
        rw [hfollow, htarget]
      constructor
      · rintro ⟨hs, hne⟩
        exact ⟨hs, hneq.mp hne⟩
      · rintro ⟨hs, hne⟩
        exact ⟨hs, hneq.mpr hne⟩
    · have hd' : BootstrapPhysicalBlock.slot w t.1 ≠ PublicDiscreteDraws.dataSlot :=
        fun h => hd (hslot.symm ▸ h)
      simp only [hd, hd', false_and]
  · simp only [hm, false_and]

private theorem step_eq_of_discovery_iff
    (v w : BootstrapPhysicalBlock.Input p s)
    (st : BootstrapPhysicalBlock.State p) (t : Fin p.T)
    (hids : v.ids = w.ids)
    (hdiscovery : BootstrapPhysicalBlock.discoveryPositive v st t ↔
      BootstrapPhysicalBlock.discoveryPositive w st t) :
    BootstrapPhysicalBlock.step v st t = BootstrapPhysicalBlock.step w st t := by
  by_cases h : BootstrapPhysicalBlock.discoveryPositive v st t
  · have h' := hdiscovery.mp h
    simp [BootstrapPhysicalBlock.step, h, h', hids]
  · have h' : ¬ BootstrapPhysicalBlock.discoveryPositive w st t :=
      fun hw => h (hdiscovery.mpr hw)
    simp [BootstrapPhysicalBlock.step, h, h']

/-- General comparison for two existing physical inputs. Equal original
local draws are represented only by their resulting arm alternatives here;
the actual-input theorem below derives those equalities from the original
round scalars. -/
theorem run_eq_of_local_support_reads
    (v w : BootstrapPhysicalBlock.Input p s)
    (j : {j // j ∈ v.uninformed}) (k : {j // j ∈ w.uninformed})
    (hactive : v.active j = true) (hactive' : w.active k = true)
    (hids : v.ids = w.ids)
    (hid : v.privateId j = w.privateId k)
    (hheld : v.held j = w.held k)
    (htarget : v.target = w.target)
    (hrowLearning : ∀ t : BlockTime p s, v.row.2 t.1 = w.row.2 t.1)
    (hfollowerAvoid : ∀ t : BlockTime p s,
      (v.followerAvoid j t.1).val = (w.followerAvoid k t.1).val)
    (hSupportTarget : supportAvoidanceVector v j v.target =
      supportAvoidanceVector w k w.target) :
    ∀ n : ℕ, BootstrapPhysicalBlock.run v n = BootstrapPhysicalBlock.run w n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    by_cases hn : n < p.T
    · let t : Fin p.T := ⟨n, hn⟩
      by_cases hblock : t ∈ calendarBlock p s
      · let bt : BlockTime p s := ⟨t, hblock⟩
        have hdiscovery :
            BootstrapPhysicalBlock.discoveryPositive v
                (BootstrapPhysicalBlock.run v n) t ↔
              BootstrapPhysicalBlock.discoveryPositive w
                (BootstrapPhysicalBlock.run v n) t := by
          simpa [t, bt] using discoveryPositive_iff_of_local_reads v w j k
            (BootstrapPhysicalBlock.run v n) bt hactive hactive' hids hid hheld
            htarget (hrowLearning bt) (hfollowerAvoid bt) hSupportTarget
        have hstep := step_eq_of_discovery_iff v w
          (BootstrapPhysicalBlock.run v n) t hids hdiscovery
        calc
          BootstrapPhysicalBlock.run v (n + 1) =
              BootstrapPhysicalBlock.step v (BootstrapPhysicalBlock.run v n) t := by
            simpa [t] using BootstrapPhysicalBlock.run_succ v t
          _ = BootstrapPhysicalBlock.step w (BootstrapPhysicalBlock.run v n) t := hstep
          _ = BootstrapPhysicalBlock.step w (BootstrapPhysicalBlock.run w n) t := by
            rw [ih]
          _ = BootstrapPhysicalBlock.run w (n + 1) := by
            symm
            simpa [t] using BootstrapPhysicalBlock.run_succ w t
      · have hnoV : ¬ BootstrapPhysicalBlock.discoveryPositive v
            (BootstrapPhysicalBlock.run v n) t := fun h => hblock h.1
        have hnoW : ¬ BootstrapPhysicalBlock.discoveryPositive w
            (BootstrapPhysicalBlock.run w n) t := fun h => hblock h.1
        calc
          BootstrapPhysicalBlock.run v (n + 1) =
              BootstrapPhysicalBlock.step v (BootstrapPhysicalBlock.run v n) t := by
                simpa [t] using BootstrapPhysicalBlock.run_succ v t
          _ = BootstrapPhysicalBlock.run v n :=
                BootstrapPhysicalBlock.step_of_no_positive v
                  (BootstrapPhysicalBlock.run v n) t hnoV
          _ = BootstrapPhysicalBlock.run w n := ih
          _ = BootstrapPhysicalBlock.step w (BootstrapPhysicalBlock.run w n) t :=
                (BootstrapPhysicalBlock.step_of_no_positive w
                  (BootstrapPhysicalBlock.run w n) t hnoW).symm
          _ = BootstrapPhysicalBlock.run w (n + 1) := by
                symm
                simpa [t] using BootstrapPhysicalBlock.run_succ w t
    · simp [BootstrapPhysicalBlock.run, hn, ih]

/-- Coordinator actions are equal at every true-row block slot when the
existing states and all coordinator-local arm draws agree. -/
private theorem coordinatorActions_eq_of_local_support_reads
    (v w : BootstrapPhysicalBlock.Input p s)
    (st : BootstrapPhysicalBlock.State p) (t : BlockTime p s)
    (hrowForward : ∀ u : Fin (A_id p), v.row.1 u t.1 = w.row.1 u t.1)
    (hrowLearning : v.row.2 t.1 = w.row.2 t.1)
    (htarget : v.target = w.target)
    (hcoordUniform : v.uniform (ActiveRoundActions.coordinator p.two_le_m) t.1 =
      w.uniform (ActiveRoundActions.coordinator p.two_le_m) t.1)
    (hcoordAvoid : (v.coordinatorAvoid t.1).val = (w.coordinatorAvoid t.1).val) :
    BootstrapPhysicalBlock.actions v st t.1
        (ActiveRoundActions.coordinator p.two_le_m) =
      BootstrapPhysicalBlock.actions w st t.1
        (ActiveRoundActions.coordinator p.two_le_m) := by
  rw [BootstrapPhysicalBlock.actions_coordinator,
    BootstrapPhysicalBlock.actions_coordinator]
  exact coordinatorAction_eq_of_local_reads v w st t hrowForward
    hrowLearning htarget hcoordUniform hcoordAvoid

/-- An actual two-player context comparison. The only state compared is the
existing physical block `State`; no incoming boundary, history, numerical
feedback, or peer-action profile is assumed equal. -/
theorem actual_local_context_reduction
    {P : CompletePublicTable.PublishedOutput p} {J : Fin (M p)}
    {x y : ReferenceInitializationRun.Input p}
    {s : Fin (n_boot p)}
    (left : ActualLocalBlock P J x s)
    (right : ActualLocalBlock P J y s)
    (hsource : left.follower.1 = right.follower.1)
    (hid : (actualPhysicalInput x left.incoming s).privateId left.follower =
      (actualPhysicalInput y right.incoming s).privateId right.follower)
    (hheld : (actualPhysicalInput x left.incoming s).held left.follower =
      (actualPhysicalInput y right.incoming s).held right.follower)
    (htarget : (actualPhysicalInput x left.incoming s).target =
      (actualPhysicalInput y right.incoming s).target)
    (hSupportHeld : supportAvoidanceVector
        (actualPhysicalInput x left.incoming s) left.follower
        ((actualPhysicalInput x left.incoming s).held left.follower) =
      supportAvoidanceVector
        (actualPhysicalInput y right.incoming s) right.follower
        ((actualPhysicalInput y right.incoming s).held right.follower))
    (hSupportTarget : supportAvoidanceVector
        (actualPhysicalInput x left.incoming s) left.follower
        (actualPhysicalInput x left.incoming s).target =
      supportAvoidanceVector
        (actualPhysicalInput y right.incoming s) right.follower
        (actualPhysicalInput y right.incoming s).target)
    (hcoordRound : ∀ t : BlockTime p s,
      BootstrapPhysicalInput.playerRoundScalarAt p x.coordinates
          (ActiveRoundActions.coordinator p.two_le_m) t.1 =
        BootstrapPhysicalInput.playerRoundScalarAt p y.coordinates
          (ActiveRoundActions.coordinator p.two_le_m) t.1)
    (hfollowerRound : ∀ t : BlockTime p s,
      BootstrapPhysicalInput.playerRoundScalarAt p x.coordinates
          (PublicDiscreteDraws.followerPlayer p.two_le_m left.follower.1) t.1 =
        BootstrapPhysicalInput.playerRoundScalarAt p y.coordinates
          (PublicDiscreteDraws.followerPlayer p.two_le_m right.follower.1) t.1) :
    actualContextMap P J x s left = actualContextMap P J y s right ∧
    (∀ n : ℕ, n ≤ p.T →
      BootstrapPhysicalBlock.run (actualPhysicalInput x left.incoming s) n =
        BootstrapPhysicalBlock.run (actualPhysicalInput y right.incoming s) n) ∧
    (∀ t : BlockTime p s,
      BootstrapPhysicalBlock.actions (actualPhysicalInput x left.incoming s)
          (BootstrapPhysicalBlock.run (actualPhysicalInput x left.incoming s) t.1)
          t.1 (ActiveRoundActions.coordinator p.two_le_m) =
        BootstrapPhysicalBlock.actions (actualPhysicalInput y right.incoming s)
          (BootstrapPhysicalBlock.run (actualPhysicalInput y right.incoming s) t.1)
          t.1 (ActiveRoundActions.coordinator p.two_le_m)) ∧
    (∀ t : BlockTime p s,
      (actualPhysicalInput x left.incoming s).ids
          ((actualPhysicalInput x left.incoming s).privateId left.follower) t.1 = false →
      (0 < (BootstrapPhysicalBlock.observationIndex
          (actualPhysicalInput x left.incoming s)
          (BootstrapPhysicalBlock.run (actualPhysicalInput x left.incoming s) t.1)
          t.1 (PublicDiscreteDraws.followerPlayer p.two_le_m left.follower.1)).val ↔
        0 < (BootstrapPhysicalBlock.observationIndex
          (actualPhysicalInput y right.incoming s)
          (BootstrapPhysicalBlock.run (actualPhysicalInput y right.incoming s) t.1)
          t.1 (PublicDiscreteDraws.followerPlayer p.two_le_m right.follower.1)).val)) ∧
    BootstrapPhysicalBlock.physicalStayGain (actualPhysicalInput x left.incoming s)
        left.follower =
      BootstrapPhysicalBlock.physicalStayGain (actualPhysicalInput y right.incoming s)
        right.follower := by
  let v := actualPhysicalInput x left.incoming s
  let w := actualPhysicalInput y right.incoming s
  have hids : v.ids = w.ids := by
    change x.ids = y.ids
    rw [left.ids_eq, right.ids_eq]
  have hrowForward : ∀ (t : BlockTime p s) (u : Fin (A_id p)),
      v.row.1 u t.1 = w.row.1 u t.1 := by
    intro t u
    change x.row.1 u t.1 = y.row.1 u t.1
    rw [left.row_eq, right.row_eq]
  have hrowLearning : ∀ t : BlockTime p s, v.row.2 t.1 = w.row.2 t.1 := by
    intro t
    change x.row.2 t.1 = y.row.2 t.1
    rw [left.row_eq, right.row_eq]
  have hcoordUniform : ∀ t : BlockTime p s,
      v.uniform (ActiveRoundActions.coordinator p.two_le_m) t.1 =
        w.uniform (ActiveRoundActions.coordinator p.two_le_m) t.1 := by
    intro t
    change BootstrapPrivateRoundStreams.fullArmScalarDraw p
        (BootstrapPhysicalInput.playerRoundScalarAt p x.coordinates
          (ActiveRoundActions.coordinator p.two_le_m) t.1) =
      BootstrapPrivateRoundStreams.fullArmScalarDraw p
        (BootstrapPhysicalInput.playerRoundScalarAt p y.coordinates
          (ActiveRoundActions.coordinator p.two_le_m) t.1)
    rw [hcoordRound t]
  have htargetDraw :
      BootstrapPrivateRoundStreams.coordinatorTargetDraw p
        (BootstrapPhysicalInput.coordinatorTargetScalarAt p s x.coordinates) =
      BootstrapPrivateRoundStreams.coordinatorTargetDraw p
        (BootstrapPhysicalInput.coordinatorTargetScalarAt p s y.coordinates) := by
    change v.target = w.target
    exact htarget
  have hcoordAvoid : ∀ t : BlockTime p s,
      (v.coordinatorAvoid t.1).val = (w.coordinatorAvoid t.1).val := by
    intro t
    change (BootstrapPrivateRoundStreams.forbiddenArmScalarDraw p
        (BootstrapPrivateRoundStreams.coordinatorTargetDraw p
          (BootstrapPhysicalInput.coordinatorTargetScalarAt p s x.coordinates))
        (BootstrapPhysicalInput.playerRoundScalarAt p x.coordinates
          (ActiveRoundActions.coordinator p.two_le_m) t.1)).val =
      (BootstrapPrivateRoundStreams.forbiddenArmScalarDraw p
        (BootstrapPrivateRoundStreams.coordinatorTargetDraw p
          (BootstrapPhysicalInput.coordinatorTargetScalarAt p s y.coordinates))
        (BootstrapPhysicalInput.playerRoundScalarAt p y.coordinates
          (ActiveRoundActions.coordinator p.two_le_m) t.1)).val
    rw [htargetDraw, hcoordRound t]
  have hfollowerAvoid : ∀ t : BlockTime p s,
      (v.followerAvoid left.follower t.1).val =
        (w.followerAvoid right.follower t.1).val := by
    intro t
    change (BootstrapPrivateRoundStreams.forbiddenArmScalarDraw p
        (v.held left.follower)
        (BootstrapPhysicalInput.playerRoundScalarAt p x.coordinates
          (PublicDiscreteDraws.followerPlayer p.two_le_m left.follower.1) t.1)).val =
      (BootstrapPrivateRoundStreams.forbiddenArmScalarDraw p
        (w.held right.follower)
        (BootstrapPhysicalInput.playerRoundScalarAt p y.coordinates
          (PublicDiscreteDraws.followerPlayer p.two_le_m right.follower.1) t.1)).val
    rw [hheld, hfollowerRound t]
  have hrun := run_eq_of_local_support_reads v w left.follower right.follower
    left.active right.active hids hid hheld htarget hrowLearning hfollowerAvoid
    hSupportTarget
  have hcoordAction : ∀ t : BlockTime p s,
      BootstrapPhysicalBlock.actions v (BootstrapPhysicalBlock.run v t.1) t.1
          (ActiveRoundActions.coordinator p.two_le_m) =
        BootstrapPhysicalBlock.actions w (BootstrapPhysicalBlock.run w t.1) t.1
          (ActiveRoundActions.coordinator p.two_le_m) := by
    intro t
    rw [hrun t.1]
    exact coordinatorActions_eq_of_local_support_reads v w
      (BootstrapPhysicalBlock.run w t.1) t (hrowForward t)
      (hrowLearning t) htarget (hcoordUniform t) (hcoordAvoid t)
  have hfeedback : ∀ t : BlockTime p s,
      v.ids (v.privateId left.follower) t.1 = false →
      (0 < BootstrapPhysicalBlock.feedback v
          (BootstrapPhysicalBlock.run v t.1) t.1
          (PublicDiscreteDraws.followerPlayer p.two_le_m left.follower.1) ↔
        0 < BootstrapPhysicalBlock.feedback w
          (BootstrapPhysicalBlock.run w t.1) t.1
          (PublicDiscreteDraws.followerPlayer p.two_le_m right.follower.1)) := by
    intro t hzero
    have hbit : v.ids (v.privateId left.follower) t.1 =
        w.ids (w.privateId right.follower) t.1 := by
      rw [hids, hid]
    have hzero' : w.ids (w.privateId right.follower) t.1 = false := by
      rw [hbit] at hzero
      exact hzero
    rw [follower_feedback_pos_iff_support v (BootstrapPhysicalBlock.run v t.1)
      left.follower t left.active hzero]
    rw [follower_feedback_pos_iff_support w (BootstrapPhysicalBlock.run w t.1)
      right.follower t right.active hzero']
    rw [congrFun hSupportHeld t]
    rw [hcoordAction t, hheld]
  have htest : ∀ t : BlockTime p s,
      v.ids (v.privateId left.follower) t.1 = false →
      (0 < (BootstrapPhysicalBlock.observationIndex v
          (BootstrapPhysicalBlock.run v t.1) t.1
          (PublicDiscreteDraws.followerPlayer p.two_le_m left.follower.1)).val ↔
        0 < (BootstrapPhysicalBlock.observationIndex w
          (BootstrapPhysicalBlock.run w t.1) t.1
          (PublicDiscreteDraws.followerPlayer p.two_le_m right.follower.1)).val) := by
    intro t hzero
    rw [BootstrapPhysicalBlock.observationIndex_pos_iff,
      BootstrapPhysicalBlock.observationIndex_pos_iff]
    exact hfeedback t hzero
  have hstayRounds :
      BootstrapPhysicalBlock.physicalStayRounds v left.follower =
        BootstrapPhysicalBlock.physicalStayRounds w right.follower := by
    apply Finset.ext
    intro t
    simp only [BootstrapPhysicalBlock.physicalStayRounds, Finset.mem_filter]
    constructor
    · rintro ⟨ht, hzero, hpositive⟩
      let bt : BlockTime p s := ⟨t, ht⟩
      have hbit : v.ids (v.privateId left.follower) t =
          w.ids (w.privateId right.follower) t := by
        rw [hids, hid]
      refine ⟨ht, ?_, ?_⟩
      · rw [← hbit]
        exact hzero
      · have hzeroBt : v.ids (v.privateId left.follower) bt.1 = false := by
          simpa [bt] using hzero
        have hpositive' := (hfeedback bt hzeroBt).mp hpositive
        simpa [bt] using hpositive'
    · rintro ⟨ht, hzero, hpositive⟩
      let bt : BlockTime p s := ⟨t, ht⟩
      have hbit : v.ids (v.privateId left.follower) t =
          w.ids (w.privateId right.follower) t := by
        rw [hids, hid]
      refine ⟨ht, ?_, ?_⟩
      · rw [hbit]
        exact hzero
      · have hzeroLeft : v.ids (v.privateId left.follower) t = false := by
          rw [hbit]
          exact hzero
        have hzeroBt : v.ids (v.privateId left.follower) bt.1 = false := by
          simpa [bt] using hzeroLeft
        have hpositive' := (hfeedback bt hzeroBt).mpr hpositive
        simpa [bt] using hpositive'
  have hgain : BootstrapPhysicalBlock.physicalStayGain v left.follower =
      BootstrapPhysicalBlock.physicalStayGain w right.follower := by
    change (if v.active left.follower = true then
        (BootstrapPhysicalBlock.physicalStayRounds v left.follower).card else 0) =
      if w.active right.follower = true then
        (BootstrapPhysicalBlock.physicalStayRounds w right.follower).card else 0
    rw [left.active, right.active, hstayRounds]
  have hsourceIndex : BootstrapPhysicalInput.sourceFollowerIndex p left.follower.1 =
      BootstrapPhysicalInput.sourceFollowerIndex p right.follower.1 :=
    congrArg (BootstrapPhysicalInput.sourceFollowerIndex p) hsource
  have hcontext : actualContextMap P J x s left = actualContextMap P J y s right := by
    dsimp only [actualContextMap]
    exact Sigma.ext rfl (heq_of_eq (Prod.ext rfl (Prod.ext hsourceIndex
      (Prod.ext hheld (Prod.ext htarget (Prod.ext hSupportHeld hSupportTarget))))))
  exact ⟨hcontext, (fun n _ => hrun n), hcoordAction, htest, hgain⟩

end Bandits.Support.GeneratedBootstrapSupportContext

end
