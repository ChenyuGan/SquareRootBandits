/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.FiniteBanditModel
public import Bandits.Support.PublicDiscreteDraws
public import Bandits.Support.OrderedTupleSampler
public import Bandits.Support.AffineChannelLaw

/-!
# Physical actions on one live assignment

Literal branch order from `sources/zip4/manuscript/05_binary_transport.tex:92-124`,
with statuses and tests from lines 71-88 and physical identities from lines 155-175.
Feedback is exactly the environment in `01_introduction.tex:20-29`.
The words use the affine map of `05_binary_transport.tex:7-21`; their encodings,
authenticity and sampling laws are external to this deterministic module.
The reply fields mentioned in `06_interruptions.tex:112-124` are not reconstructed here.

`Snapshot a` concerns ONE LIVE assignment. Every occupied follower's fields are
those of `a`; proving that scope restriction for a chronological protocol remains
the decoder/current-record owner's obligation. `RoundInput` supplies deterministic
coordinates, current words and a fast arm outside the slow image. It asserts no
collision freedom, independence, distribution, decoder correctness or queue law.
This is internal mathematics, not a frozen anchor or manuscript-lemma closure.
-/

@[expose] public section

namespace Bandits.Support.ActiveRoundActions

open FiniteBanditModel PublicDiscreteDraws AffineChannelLaw

/-- The existing follower carrier: index `j` denotes source player `j.val + 1`. -/
abbrev Follower (m : ℕ) := Fin (followerCount m)

/-- The source has exactly these three follower statuses. -/
inductive FollowerStatus where
  | unoccupied
  | pending
  | released
  deriving DecidableEq

/-- Pending and released are the source's occupied states. -/
def FollowerStatus.occupied (status : FollowerStatus) : Prop :=
  status = .pending ∨ status = .released

/-- Current injective slow assignment and auxiliary arm outside its image. -/
structure Assignment (m K : ℕ) where
  assigned : Follower m → Arm K
  injective : Function.Injective assigned
  auxiliary : Arm K
  auxiliary_outside : ∀ j, auxiliary ≠ assigned j

/-- Arm-choice snapshot restricted to occupied fields matching `a`.
No assertion about arbitrary histories or decoded records is bundled here. -/
structure Snapshot {m K : ℕ} (a : Assignment m K) where
  missing : Finset (Follower m)
  status : Follower m → FollowerStatus

/-- A supplied currently sent word and its supplied affine coefficients/offset. -/
structure HashedWord (B : ℕ) where
  sample : Sample B
  word : Word B

/-- The actual affine bit of the supplied word, with no probabilistic claim. -/
def HashedWord.bit {B : ℕ} (w : HashedWord B) : Bit := affineHash w.sample w.word

/-- One deterministic input round. DOWN/UP words concern the selected follower.
Unused coordinates are harmless supplied data; the fast arm has no asserted law. -/
structure RoundInput {m K : ℕ} (a : Assignment m K) (B : ℕ) where
  slot : Slot
  selected : Follower m
  tuple : OrderedTupleSampler.Tuple m K
  pilots : Player m → Arm K
  down : HashedWord B
  up : HashedWord B
  fast : Arm K
  fast_outside : ∀ j, fast ≠ a.assigned j

/-- An arbitrary already rounded, if needed, reward row in `[0,1]`. -/
abbrev RewardRow (K : ℕ) := {r : Arm K → ℝ // ∀ a, r a ∈ Set.Icc (0 : ℝ) 1}

variable {m K B : ℕ} {a : Assignment m K}

/-- Player zero in the existing player carrier. -/
def coordinator (hm : 2 ≤ m) : Player m := ⟨0, by omega⟩

theorem followerPlayer_injective (hm : 2 ≤ m) :
    Function.Injective (followerPlayer hm) := by
  intro i j hij
  apply Fin.ext
  have hv := congrArg Fin.val hij
  simp only [followerPlayer_val] at hv
  omega

theorem followerPlayer_ne_coordinator (hm : 2 ≤ m) (j : Follower m) :
    followerPlayer hm j ≠ coordinator hm := by
  intro h
  have hv := congrArg Fin.val h
  simp only [followerPlayer_val, coordinator, Fin.val_mk] at hv
  omega

/-- Recover the follower index of a nonzero player. -/
def followerIndex (hm : 2 ≤ m) (p : Player m) (hp : p ≠ coordinator hm) : Follower m :=
  ⟨p.val - 1, by
    have hpos : p.val ≠ 0 := by
      intro h
      apply hp
      exact Fin.ext h
    have := p.isLt
    simp only [followerCount]
    omega⟩

theorem followerPlayer_followerIndex (hm : 2 ≤ m) (p : Player m)
    (hp : p ≠ coordinator hm) : followerPlayer hm (followerIndex hm p hp) = p := by
  apply Fin.ext
  have hpos : p.val ≠ 0 := by
    intro h
    exact hp (Fin.ext h)
  simp only [followerPlayer_val, followerIndex]
  omega

theorem followerIndex_followerPlayer (hm : 2 ≤ m) (j : Follower m)
    (hp : followerPlayer hm j ≠ coordinator hm) :
    followerIndex hm (followerPlayer hm j) hp = j := by
  apply Fin.ext
  simp only [followerIndex, followerPlayer_val, Fin.val_mk, Nat.add_sub_cancel]

theorem player_cases (hm : 2 ≤ m) (p : Player m) :
    p = coordinator hm ∨ ∃ j, p = followerPlayer hm j := by
  by_cases hp : p = coordinator hm
  · exact Or.inl hp
  · exact Or.inr ⟨followerIndex hm p hp, (followerPlayer_followerIndex hm p hp).symm⟩

theorem assigned_ne (i j : Follower m) (hij : i ≠ j) :
    a.assigned i ≠ a.assigned j := fun h => hij (a.injective h)

theorem tuple_coordinator_ne_follower (hm : 2 ≤ m) (r : RoundInput a B)
    (j : Follower m) : r.tuple.val (coordinator hm) ≠ r.tuple.val (followerPlayer hm j) :=
  fun h => followerPlayer_ne_coordinator hm j (r.tuple.property h).symm

theorem tuple_followers_ne (hm : 2 ≤ m) (r : RoundInput a B)
    (i j : Follower m) (hij : i ≠ j) :
    r.tuple.val (followerPlayer hm i) ≠ r.tuple.val (followerPlayer hm j) :=
  fun h => hij (followerPlayer_injective hm (r.tuple.property h))

/-- Source SendArm: zero collides at the receiver, one uses the sender arm. -/
def sendArm (bit : Bit) (send receive : Arm K) : Arm K :=
  if bit = 0 then receive else send

theorem sendArm_zero (send receive : Arm K) : sendArm 0 send receive = receive := by
  simp only [sendArm, ite_true]

theorem sendArm_one (send receive : Arm K) : sendArm 1 send receive = send := by
  simp only [sendArm, one_ne_zero, ite_false]

/-- Coordinator branch priority, including fast play on EVERY slot when `P = ∅`. -/
def coordinatorAction (hm : 2 ≤ m) (s : Snapshot a) (r : RoundInput a B) : Arm K :=
  if s.missing = ∅ then r.fast
  else if r.slot = dataSlot then r.pilots (coordinator hm)
  else if r.slot = downSlot ∧ r.selected ∈ s.missing then
    sendArm r.down.bit (r.tuple.val (coordinator hm))
      (r.tuple.val (followerPlayer hm r.selected))
  else r.tuple.val (coordinator hm)

/-- Follower branch priority from source lines 106-121; occupied fields belong to `a`. -/
def followerAction (hm : 2 ≤ m) (s : Snapshot a) (r : RoundInput a B)
    (j : Follower m) : Arm K :=
  if s.status j = .unoccupied then
    if r.slot = dataSlot then r.pilots (followerPlayer hm j)
    else if r.slot = upSlot ∧ r.selected = j then
      sendArm r.up.bit (r.tuple.val (followerPlayer hm j)) (r.tuple.val (coordinator hm))
    else r.tuple.val (followerPlayer hm j)
  else if s.status j = .released ∨ r.slot = dataSlot then a.assigned j
  else if r.slot = upSlot ∧ r.selected = j ∧ r.tuple.val (coordinator hm) = a.auxiliary then
    a.auxiliary
  else if (r.slot = downSlot ∧ a.assigned j = r.tuple.val (followerPlayer hm r.selected)) ∨
      (r.slot = upSlot ∧ a.assigned j = r.tuple.val (coordinator hm)) then a.auxiliary
  else a.assigned j

/-- Simultaneous physical arm profile on the existing player carrier. -/
def actions (hm : 2 ≤ m) (s : Snapshot a) (r : RoundInput a B) : ActionProfile m K :=
  fun p => if hp : p = coordinator hm then coordinatorAction hm s r
    else followerAction hm s r (followerIndex hm p hp)

theorem actions_coordinator (hm : 2 ≤ m) (s : Snapshot a) (r : RoundInput a B) :
    actions hm s r (coordinator hm) = coordinatorAction hm s r := by
  simp only [actions, dite_true]

theorem actions_follower (hm : 2 ≤ m) (s : Snapshot a) (r : RoundInput a B)
    (j : Follower m) : actions hm s r (followerPlayer hm j) = followerAction hm s r j := by
  simp only [actions, dite_eq_right (followerPlayer_ne_coordinator hm j),
    followerIndex_followerPlayer]

/-- Feedback is ONLY the accepted physical environment, evaluated on this profile. -/
noncomputable def feedback (hm : 2 ≤ m) (s : Snapshot a) (r : RoundInput a B)
    (row : RewardRow K) (p : Player m) : ℝ :=
  playerFeedback (actions hm s r) row.val p

theorem feedback_mem_Icc (hm : 2 ≤ m) (s : Snapshot a) (r : RoundInput a B)
    (row : RewardRow K) (p : Player m) : feedback hm s r row p ∈ Set.Icc (0 : ℝ) 1 :=
  playerFeedback_mem_Icc_of_bounds _ _ row.property p

theorem feedback_eq_zero_of_collision (hm : 2 ≤ m) (s : Snapshot a)
    (r : RoundInput a B) (row : RewardRow K) (p q : Player m) (hqp : q ≠ p)
    (hsame : actions hm s r q = actions hm s r p) : feedback hm s r row p = 0 := by
  have hcollision : ¬ collisionFreeFor (actions hm s r) p := fun h => h q hqp hsame
  simp only [feedback, playerFeedback, ite_eq_right hcollision]

theorem feedback_eq_reward_of_collision_free (hm : 2 ≤ m) (s : Snapshot a)
    (r : RoundInput a B) (row : RewardRow K) (p : Player m)
    (hfree : collisionFreeFor (actions hm s r) p) :
    feedback hm s r row p = row.val (actions hm s r p) := by
  simp only [feedback, playerFeedback, ite_eq_left hfree]

theorem coordinatorAction_fast (hm : 2 ≤ m) (s : Snapshot a) (r : RoundInput a B)
    (hmissing : s.missing = ∅) : coordinatorAction hm s r = r.fast := by
  simp only [coordinatorAction, ite_eq_left hmissing]

theorem coordinatorAction_data (hm : 2 ≤ m) (s : Snapshot a) (r : RoundInput a B)
    (hmissing : s.missing ≠ ∅) (hslot : r.slot = dataSlot) :
    coordinatorAction hm s r = r.pilots (coordinator hm) := by
  simp only [coordinatorAction, ite_eq_right hmissing, ite_eq_left hslot]

theorem missing_ne_empty_of_mem (s : Snapshot a) (j : Follower m)
    (hj : j ∈ s.missing) : s.missing ≠ ∅ := by
  intro he
  rw [he] at hj
  exact Finset.notMem_empty j hj

theorem coordinatorAction_down (hm : 2 ≤ m) (s : Snapshot a) (r : RoundInput a B)
    (hslot : r.slot = downSlot) (hmissing : r.selected ∈ s.missing) :
    coordinatorAction hm s r = sendArm r.down.bit (r.tuple.val (coordinator hm))
      (r.tuple.val (followerPlayer hm r.selected)) := by
  have hnotdata : r.slot ≠ dataSlot := by rw [hslot]; decide
  simp only [coordinatorAction, ite_eq_right (missing_ne_empty_of_mem s _ hmissing),
    ite_eq_right hnotdata, ite_eq_left (And.intro hslot hmissing)]

theorem coordinatorAction_up (hm : 2 ≤ m) (s : Snapshot a) (r : RoundInput a B)
    (hmissing : s.missing ≠ ∅) (hslot : r.slot = upSlot) :
    coordinatorAction hm s r = r.tuple.val (coordinator hm) := by
  have hnotdata : r.slot ≠ dataSlot := by rw [hslot]; decide
  have hnotdown : r.slot ≠ downSlot := by rw [hslot]; decide
  simp only [coordinatorAction, ite_eq_right hmissing, ite_eq_right hnotdata, hnotdown,
    false_and, ite_false]

theorem followerAction_unoccupied_data (hm : 2 ≤ m) (s : Snapshot a)
    (r : RoundInput a B) (j : Follower m) (hj : s.status j = .unoccupied)
    (hslot : r.slot = dataSlot) :
    followerAction hm s r j = r.pilots (followerPlayer hm j) := by
  simp only [followerAction, ite_eq_left hj, ite_eq_left hslot]

theorem followerAction_unoccupied_down (hm : 2 ≤ m) (s : Snapshot a)
    (r : RoundInput a B) (j : Follower m) (hj : s.status j = .unoccupied)
    (hslot : r.slot = downSlot) :
    followerAction hm s r j = r.tuple.val (followerPlayer hm j) := by
  have hnotdata : r.slot ≠ dataSlot := by rw [hslot]; decide
  have hnotup : r.slot ≠ upSlot := by rw [hslot]; decide
  simp only [followerAction, ite_eq_left hj, ite_eq_right hnotdata, hnotup, false_and, ite_false]

theorem followerAction_unoccupied_up_selected (hm : 2 ≤ m) (s : Snapshot a)
    (r : RoundInput a B) (hj : s.status r.selected = .unoccupied)
    (hslot : r.slot = upSlot) :
    followerAction hm s r r.selected = sendArm r.up.bit
      (r.tuple.val (followerPlayer hm r.selected)) (r.tuple.val (coordinator hm)) := by
  have hnotdata : r.slot ≠ dataSlot := by rw [hslot]; decide
  rw [followerAction, ite_eq_left hj, ite_eq_right hnotdata, ite_eq_left ⟨hslot, rfl⟩]

theorem followerAction_released (hm : 2 ≤ m) (s : Snapshot a) (r : RoundInput a B)
    (j : Follower m) (hj : s.status j = .released) :
    followerAction hm s r j = a.assigned j := by
  have hnot : s.status j ≠ .unoccupied := by rw [hj]; decide
  rw [followerAction, ite_eq_right hnot, ite_eq_left (Or.inl hj)]

theorem followerAction_occupied_data (hm : 2 ≤ m) (s : Snapshot a)
    (r : RoundInput a B) (j : Follower m) (hj : (s.status j).occupied)
    (hslot : r.slot = dataSlot) : followerAction hm s r j = a.assigned j := by
  rcases hj with hj | hj
  · have hnot : s.status j ≠ .unoccupied := by rw [hj]; decide
    rw [followerAction, ite_eq_right hnot, ite_eq_left (Or.inr hslot)]
  · exact followerAction_released hm s r j hj

theorem followerAction_pending_up_test (hm : 2 ≤ m) (s : Snapshot a)
    (r : RoundInput a B) (hj : s.status r.selected = .pending)
    (hslot : r.slot = upSlot) (he : r.tuple.val (coordinator hm) = a.auxiliary) :
    followerAction hm s r r.selected = a.auxiliary := by
  have hnotdata : r.slot ≠ dataSlot := by rw [hslot]; decide
  have hnotu : s.status r.selected ≠ .unoccupied := by rw [hj]; decide
  have hnotr : s.status r.selected ≠ .released := by rw [hj]; decide
  rw [followerAction, ite_eq_right hnotu,
    ite_eq_right (not_or.mpr ⟨hnotr, hnotdata⟩), ite_eq_left ⟨hslot, rfl, he⟩]

theorem followerAction_pending_down (hm : 2 ≤ m) (s : Snapshot a)
    (r : RoundInput a B) (j : Follower m) (hj : s.status j = .pending)
    (hslot : r.slot = downSlot) :
    followerAction hm s r j =
      if a.assigned j = r.tuple.val (followerPlayer hm r.selected) then a.auxiliary
      else a.assigned j := by
  have hnotdata : r.slot ≠ dataSlot := by rw [hslot]; decide
  have hnotup : r.slot ≠ upSlot := by rw [hslot]; decide
  have hnotu : s.status j ≠ .unoccupied := by rw [hj]; decide
  have hnotr : s.status j ≠ .released := by rw [hj]; decide
  rw [followerAction, ite_eq_right hnotu, ite_eq_right (not_or.mpr ⟨hnotr, hnotdata⟩),
    ite_eq_right (fun h => hnotup h.1)]
  simp only [hslot, show downSlot ≠ upSlot by decide, false_and, true_and, or_false]

/-- Identity (2): every pending follower physically avoids the selected DOWN arm.
This stronger one-round fact does not require that the selection is missing. -/
theorem pending_avoids_down (hm : 2 ≤ m) (s : Snapshot a) (r : RoundInput a B)
    (j : Follower m) (hj : s.status j = .pending) (hslot : r.slot = downSlot) :
    followerAction hm s r j ≠ r.tuple.val (followerPlayer hm r.selected) := by
  rw [followerAction_pending_down hm s r j hj hslot]
  split
  · next heq => exact fun h => a.auxiliary_outside j (h.trans heq.symm)
  · next hne => exact hne

/-- Identity (1), DATA test: the coordinator and pending follower collide on `a_j`. -/
theorem pending_data_test_feedback_zero (hm : 2 ≤ m) (s : Snapshot a)
    (r : RoundInput a B) (row : RewardRow K) (j : Follower m)
    (hmissing : s.missing ≠ ∅) (hj : s.status j = .pending)
    (hslot : r.slot = dataSlot) (hpilot : r.pilots (coordinator hm) = a.assigned j) :
    feedback hm s r row (followerPlayer hm j) = 0 := by
  apply feedback_eq_zero_of_collision hm s r row _ (coordinator hm)
    (followerPlayer_ne_coordinator hm j).symm
  rw [actions_coordinator, actions_follower, coordinatorAction_data hm s r hmissing hslot,
    followerAction_occupied_data hm s r j (Or.inl hj) hslot, hpilot]

/-- Identity (1), UP test: the coordinator and selected pending follower collide on `e`. -/
theorem pending_up_test_feedback_zero (hm : 2 ≤ m) (s : Snapshot a)
    (r : RoundInput a B) (row : RewardRow K) (hmissing : s.missing ≠ ∅)
    (hj : s.status r.selected = .pending) (hslot : r.slot = upSlot)
    (he : r.tuple.val (coordinator hm) = a.auxiliary) :
    feedback hm s r row (followerPlayer hm r.selected) = 0 := by
  apply feedback_eq_zero_of_collision hm s r row _ (coordinator hm)
    (followerPlayer_ne_coordinator hm r.selected).symm
  rw [actions_coordinator, actions_follower, coordinatorAction_up hm s r hmissing hslot,
    followerAction_pending_up_test hm s r hj hslot he, he]

/-- The release observation of source lines 83-88, evaluated before any decoder update. -/
def releaseObservation (hm : 2 ≤ m) (s : Snapshot a) (r : RoundInput a B)
    (row : RewardRow K) (j : Follower m) : Prop :=
  0 < feedback hm s r row (followerPlayer hm j) ∧
    ((r.slot = upSlot ∧ r.selected = j ∧ r.tuple.val (coordinator hm) = a.auxiliary) ∨
      (r.slot = dataSlot ∧ r.pilots (coordinator hm) = a.assigned j))

theorem no_releaseObservation_while_missing (hm : 2 ≤ m) (s : Snapshot a)
    (r : RoundInput a B) (row : RewardRow K) (j : Follower m)
    (hmissing : s.missing ≠ ∅) (hj : s.status j = .pending) :
    ¬ releaseObservation hm s r row j := by
  rintro ⟨hpos, htest⟩
  have hzero : feedback hm s r row (followerPlayer hm j) = 0 := by
    rcases htest with ⟨hslot, hselected, he⟩ | ⟨hslot, hpilot⟩
    · subst j
      exact pending_up_test_feedback_zero hm s r row hmissing hj hslot he
    · exact pending_data_test_feedback_zero hm s r row j hmissing hj hslot hpilot
  rw [hzero] at hpos
  exact (lt_irrefl 0) hpos

/-- The genuine induction assertion, stated explicitly rather than bundled into snapshots. -/
def no_released_while_missing (s : Snapshot a) : Prop :=
  s.missing ≠ ∅ → ∀ j, s.status j ≠ .released

/-- Other followers avoid the selected DOWN tuple arm, using the explicit invariant. -/
theorem other_follower_avoids_down_target (hm : 2 ≤ m) (s : Snapshot a)
    (r : RoundInput a B) (hslot : r.slot = downSlot)
    (hmissing : r.selected ∈ s.missing) (hinv : no_released_while_missing s)
    (j : Follower m) (hji : j ≠ r.selected) :
    followerAction hm s r j ≠ r.tuple.val (followerPlayer hm r.selected) := by
  have hnrel := hinv (missing_ne_empty_of_mem s _ hmissing) j
  cases hj : s.status j with
  | unoccupied =>
      rw [followerAction_unoccupied_down hm s r j hj hslot]
      exact tuple_followers_ne hm r j r.selected hji
  | pending => exact pending_avoids_down hm s r j hj hslot
  | released => exact False.elim (hnrel hj)

/-- With target unoccupied and hash zero, the coordinator physically collides with it. -/
theorem unoccupied_down_zero_collision (hm : 2 ≤ m) (s : Snapshot a)
    (r : RoundInput a B) (hslot : r.slot = downSlot)
    (hmissing : r.selected ∈ s.missing) (hj : s.status r.selected = .unoccupied)
    (hbit : r.down.bit = 0) :
    actions hm s r (coordinator hm) = actions hm s r (followerPlayer hm r.selected) := by
  rw [actions_coordinator, actions_follower, coordinatorAction_down hm s r hslot hmissing,
    followerAction_unoccupied_down hm s r r.selected hj hslot, hbit, sendArm_zero]

/-- With target unoccupied and hash one, it is alone on its tuple arm. -/
theorem unoccupied_down_one_collision_free (hm : 2 ≤ m) (s : Snapshot a)
    (r : RoundInput a B) (hslot : r.slot = downSlot)
    (hmissing : r.selected ∈ s.missing) (hinv : no_released_while_missing s)
    (hj : s.status r.selected = .unoccupied) (hbit : r.down.bit = 1) :
    collisionFreeFor (actions hm s r) (followerPlayer hm r.selected) := by
  intro p hp
  rw [actions_follower, followerAction_unoccupied_down hm s r r.selected hj hslot]
  rcases player_cases hm p with hcoord | ⟨j, hfollow⟩
  · rw [hcoord, actions_coordinator, coordinatorAction_down hm s r hslot hmissing,
      hbit, sendArm_one]
    exact tuple_coordinator_ne_follower hm r r.selected
  · have hji : j ≠ r.selected := by
      intro heq
      exact hp (hfollow.trans (congrArg (followerPlayer hm) heq))
    rw [hfollow, actions_follower]
    exact other_follower_avoids_down_target hm s r hslot hmissing hinv j hji

/-- A binary affine value has precisely the source's two alternatives. -/
theorem bit_eq_zero_or_one (b : Bit) : b = 0 ∨ b = 1 := by
  have hb := ZMod.val_lt b
  have hv : b.val = 0 ∨ b.val = 1 := by omega
  rcases hv with hv | hv
  · left
    calc
      b = (b.val : Bit) := (ZMod.natCast_zmod_val b).symm
      _ = 0 := by rw [hv]; rfl
  · right
    calc
      b = (b.val : Bit) := (ZMod.natCast_zmod_val b).symm
      _ = 1 := by rw [hv]; rfl

/-- Identity (3a), derived from physical actions and the explicit no-released invariant. -/
theorem unoccupied_down_feedback (hm : 2 ≤ m) (s : Snapshot a)
    (r : RoundInput a B) (row : RewardRow K) (hslot : r.slot = downSlot)
    (hmissing : r.selected ∈ s.missing) (hinv : no_released_while_missing s)
    (hj : s.status r.selected = .unoccupied) :
    feedback hm s r row (followerPlayer hm r.selected) =
      if r.down.bit = 1 then row.val (r.tuple.val (followerPlayer hm r.selected)) else 0 := by
  rcases bit_eq_zero_or_one r.down.bit with hbit | hbit
  · have hzero := feedback_eq_zero_of_collision hm s r row
      (followerPlayer hm r.selected) (coordinator hm)
      (followerPlayer_ne_coordinator hm r.selected).symm
      (unoccupied_down_zero_collision hm s r hslot hmissing hj hbit)
    simpa only [hbit, zero_ne_one, ite_false] using hzero
  · rw [ite_eq_left hbit, feedback_eq_reward_of_collision_free hm s r row _
      (unoccupied_down_one_collision_free hm s r hslot hmissing hinv hj hbit),
      actions_follower, followerAction_unoccupied_down hm s r r.selected hj hslot]

/-- With target pending and hash zero, the coordinator is alone on the receive arm. -/
theorem pending_down_zero_coordinator_collision_free (hm : 2 ≤ m) (s : Snapshot a)
    (r : RoundInput a B) (hslot : r.slot = downSlot)
    (hmissing : r.selected ∈ s.missing) (hinv : no_released_while_missing s)
    (hi : s.status r.selected = .pending) (hbit : r.down.bit = 0) :
    collisionFreeFor (actions hm s r) (coordinator hm) := by
  intro p hp
  rw [actions_coordinator, coordinatorAction_down hm s r hslot hmissing, hbit, sendArm_zero]
  rcases player_cases hm p with hcoord | ⟨j, hfollow⟩
  · exact False.elim (hp hcoord)
  · rw [hfollow, actions_follower]
    by_cases hji : j = r.selected
    · subst j
      exact pending_avoids_down hm s r r.selected hi hslot
    · exact other_follower_avoids_down_target hm s r hslot hmissing hinv j hji

/-- Identity (3b): pending target and zero hash give the coordinator the receive-arm reward. -/
theorem pending_down_coordinator_feedback (hm : 2 ≤ m) (s : Snapshot a)
    (r : RoundInput a B) (row : RewardRow K) (hslot : r.slot = downSlot)
    (hmissing : r.selected ∈ s.missing) (hinv : no_released_while_missing s)
    (hi : s.status r.selected = .pending) (hbit : r.down.bit = 0) :
    feedback hm s r row (coordinator hm) =
      row.val (r.tuple.val (followerPlayer hm r.selected)) := by
  rw [feedback_eq_reward_of_collision_free hm s r row _
    (pending_down_zero_coordinator_collision_free hm s r hslot hmissing hinv hi hbit),
    actions_coordinator, coordinatorAction_down hm s r hslot hmissing, hbit, sendArm_zero]

/-- Confirmation from source lines 75-79, using status and `P` before arm choice. -/
def confirmation (hm : 2 ≤ m) (s : Snapshot a) (r : RoundInput a B)
    (row : RewardRow K) (j : Follower m) : Prop :=
  r.slot = downSlot ∧ r.selected = j ∧ j ∈ s.missing ∧ r.down.bit = 0 ∧
    0 < feedback hm s r row (coordinator hm)

/-- Identity (4): a confirmation physically rules out an unoccupied target.
No no-released invariant is needed for this stronger one-round implication. -/
theorem confirmation_implies_occupied (hm : 2 ≤ m) (s : Snapshot a)
    (r : RoundInput a B) (row : RewardRow K) (j : Follower m)
    (hconfirm : confirmation hm s r row j) : (s.status j).occupied := by
  rcases hconfirm with ⟨hslot, hselected, hmissing, hbit, hpos⟩
  subst j
  cases hj : s.status r.selected with
  | unoccupied =>
      have hzero := feedback_eq_zero_of_collision hm s r row
        (coordinator hm) (followerPlayer hm r.selected)
        (followerPlayer_ne_coordinator hm r.selected)
        (unoccupied_down_zero_collision hm s r hslot hmissing hj hbit).symm
      rw [hzero] at hpos
      exact False.elim ((lt_irrefl 0) hpos)
  | pending => exact Or.inl rfl
  | released => exact Or.inr rfl

/-- A confirmation targets a pending follower under the genuine induction invariant. -/
theorem confirmation_implies_pending (hm : 2 ≤ m) (s : Snapshot a)
    (r : RoundInput a B) (row : RewardRow K) (j : Follower m)
    (hinv : no_released_while_missing s) (hc : confirmation hm s r row j) :
    s.status j = .pending := by
  rcases confirmation_implies_occupied hm s r row j hc with hp | hr
  · exact hp
  · exact False.elim (hinv (missing_ne_empty_of_mem s j hc.2.2.1) j hr)

/-!
The following is only the status/missing-set projection of a finite LIVE segment,
with no cutoff, assignment change, scheduler, decoder, recorder or queue semantics.
Source end-of-round order is `06_interruptions.tex:270-295`: DOWN acceptance,
then confirmation/release, with release eligibility fixed at arm choice.
The arbitrary acceptance flags below mean acceptance of THIS current live record;
no theorem here certifies those flags or authenticates any received word.
-/

/-- Initially no follower has decoded, and every confirmation is missing. -/
def initialSnapshot (a : Assignment m K) : Snapshot a :=
  ⟨Finset.univ, fun _ => .unoccupied⟩

theorem initialSnapshot_no_released (a : Assignment m K) :
    no_released_while_missing (initialSnapshot a) := by
  intro _ j
  change FollowerStatus.unoccupied ≠ .released
  decide

/-- First apply external current-record acceptance, only to an unoccupied selected
DOWN follower. The flag supplies no decoder/authenticity claim. -/
def statusAfterAcceptance (s : Snapshot a) (r : RoundInput a B)
    (acceptCurrent : Follower m → Bool) (j : Follower m) : FollowerStatus :=
  if s.status j = .unoccupied ∧ r.slot = downSlot ∧ r.selected = j ∧ acceptCurrent j = true
  then .pending else s.status j

/-- Then update confirmations and releases from the original physical observations.
The release guard uses the PRE-CHOICE status, so a new acceptance cannot release
in the same round. These are the live-segment projections of source lines 286-295. -/
noncomputable def finishLiveRound (hm : 2 ≤ m) (s : Snapshot a) (r : RoundInput a B)
    (row : RewardRow K) (acceptCurrent : Follower m → Bool) : Snapshot a := by
  classical
  let decoded := statusAfterAcceptance s r acceptCurrent
  exact {
    missing := if confirmation hm s r row r.selected then s.missing.erase r.selected
      else s.missing
    status := fun j => if s.status j = .pending ∧ releaseObservation hm s r row j
      then .released else decoded j
  }

theorem finishLiveRound_missing_subset (hm : 2 ≤ m) (s : Snapshot a)
    (r : RoundInput a B) (row : RewardRow K) (acceptCurrent : Follower m → Bool) :
    (finishLiveRound hm s r row acceptCurrent).missing ⊆ s.missing := by
  classical
  change (if confirmation hm s r row r.selected then s.missing.erase r.selected
    else s.missing) ⊆ s.missing
  split
  · exact Finset.erase_subset _ _
  · exact Finset.Subset.refl _

/-- Acceptance cannot itself introduce a released follower. -/
theorem statusAfterAcceptance_ne_released (s : Snapshot a) (r : RoundInput a B)
    (acceptCurrent : Follower m → Bool) (j : Follower m)
    (hj : s.status j ≠ .released) :
    statusAfterAcceptance s r acceptCurrent j ≠ .released := by
  unfold statusAfterAcceptance
  split
  · decide
  · exact hj

/-- One live status/confirmation update preserves no premature release.
No restriction on the external acceptance flags is needed. -/
theorem finishLiveRound_no_released (hm : 2 ≤ m) (s : Snapshot a)
    (r : RoundInput a B) (row : RewardRow K) (acceptCurrent : Follower m → Bool)
    (hinv : no_released_while_missing s) :
    no_released_while_missing (finishLiveRound hm s r row acceptCurrent) := by
  classical
  intro hmissing j
  have hold : s.missing ≠ ∅ := by
    intro hempty
    have hsub := finishLiveRound_missing_subset hm s r row acceptCurrent
    rw [hempty] at hsub
    exact hmissing (Finset.subset_empty.mp hsub)
  have hnobs : ¬ (s.status j = .pending ∧ releaseObservation hm s r row j) := by
    rintro ⟨hj, hobs⟩
    exact no_releaseObservation_while_missing hm s r row j hold hj hobs
  change (if s.status j = .pending ∧ releaseObservation hm s r row j then .released
    else statusAfterAcceptance s r acceptCurrent j) ≠ .released
  rw [ite_eq_right hnobs]
  exact statusAfterAcceptance_ne_released s r acceptCurrent j (hinv hold j)

/-- A newly accepted follower stays pending this round: release uses old status. -/
theorem finishLiveRound_new_acceptance_pending (hm : 2 ≤ m) (s : Snapshot a)
    (r : RoundInput a B) (row : RewardRow K) (acceptCurrent : Follower m → Bool)
    (j : Follower m) (hj : s.status j = .unoccupied) (hslot : r.slot = downSlot)
    (hselected : r.selected = j) (haccept : acceptCurrent j = true) :
    (finishLiveRound hm s r row acceptCurrent).status j = .pending := by
  classical
  have hnpend : s.status j ≠ .pending := by rw [hj]; decide
  change (if s.status j = .pending ∧ releaseObservation hm s r row j then .released
    else statusAfterAcceptance s r acceptCurrent j) = .pending
  rw [ite_eq_right (fun h => hnpend h.1), statusAfterAcceptance,
    ite_eq_left ⟨hj, hslot, hselected, haccept⟩]

/-- An arbitrary external trace entry, restricted to this same live assignment. -/
structure LiveRoundData (a : Assignment m K) (B : ℕ) where
  input : RoundInput a B
  rewards : RewardRow K
  acceptCurrent : Follower m → Bool

/-- Finite live-segment state projection after every supplied round, in order. -/
noncomputable def liveSegment (hm : 2 ≤ m) (rounds : List (LiveRoundData a B)) :
    Snapshot a :=
  rounds.foldl (fun s d => finishLiveRound hm s d.input d.rewards d.acceptCurrent)
    (initialSnapshot a)

/-- The status invariant is preserved from any valid starting snapshot. -/
theorem foldl_finishLiveRound_no_released (hm : 2 ≤ m)
    (rounds : List (LiveRoundData a B)) (s : Snapshot a)
    (hinv : no_released_while_missing s) :
    no_released_while_missing
      (rounds.foldl (fun s d => finishLiveRound hm s d.input d.rewards d.acceptCurrent) s) := by
  induction rounds generalizing s with
  | nil => exact hinv
  | cons d ds ih =>
      exact ih _ (finishLiveRound_no_released hm s d.input d.rewards d.acceptCurrent hinv)

/-- No follower is released while confirmations remain missing in any finite live
segment from all-unoccupied/P=all, for arbitrary current-record acceptance flags. -/
theorem liveSegment_no_released (hm : 2 ≤ m) (rounds : List (LiveRoundData a B)) :
    no_released_while_missing (liveSegment hm rounds) :=
  foldl_finishLiveRound_no_released hm rounds _ (initialSnapshot_no_released a)

/-- In particular the invariant holds at every finite prefix, including arm choice
for the following round. This asserts only the status/confirmation projection. -/
theorem liveSegment_prefix_no_released (hm : 2 ≤ m) (rounds : List (LiveRoundData a B))
    (t : ℕ) : no_released_while_missing (liveSegment hm (rounds.take t)) :=
  liveSegment_no_released hm _

/-- The unoccupied-target identity at the next arm choice after any supplied finite
live segment; its no-released premise has now been proved by induction. -/
theorem liveSegment_unoccupied_down_feedback (hm : 2 ≤ m)
    (rounds : List (LiveRoundData a B)) (r : RoundInput a B) (row : RewardRow K)
    (hslot : r.slot = downSlot) (hmissing : r.selected ∈ (liveSegment hm rounds).missing)
    (hj : (liveSegment hm rounds).status r.selected = .unoccupied) :
    feedback hm (liveSegment hm rounds) r row (followerPlayer hm r.selected) =
      if r.down.bit = 1 then row.val (r.tuple.val (followerPlayer hm r.selected)) else 0 :=
  unoccupied_down_feedback hm _ r row hslot hmissing (liveSegment_no_released hm rounds) hj

/-- The pending-target coordinator identity after any supplied finite live segment. -/
theorem liveSegment_pending_down_coordinator_feedback (hm : 2 ≤ m)
    (rounds : List (LiveRoundData a B)) (r : RoundInput a B) (row : RewardRow K)
    (hslot : r.slot = downSlot) (hmissing : r.selected ∈ (liveSegment hm rounds).missing)
    (hj : (liveSegment hm rounds).status r.selected = .pending) (hbit : r.down.bit = 0) :
    feedback hm (liveSegment hm rounds) r row (coordinator hm) =
      row.val (r.tuple.val (followerPlayer hm r.selected)) :=
  pending_down_coordinator_feedback hm _ r row hslot hmissing
    (liveSegment_no_released hm rounds) hj hbit

end Bandits.Support.ActiveRoundActions
