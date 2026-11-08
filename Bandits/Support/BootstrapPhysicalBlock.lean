/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ActiveRoundActions
public import Bandits.Support.AffineBatchDecoder
public import Bandits.Support.BootstrapBlockConstruction
public import Bandits.Support.CompletePublicTable
public import Bandits.Support.RealRewardGridCount

/-!
# A deterministic physical reference bootstrap block

Sources: `07_public_setup.tex:27-38,52-118,125-142`,
`05_binary_transport.tex:11-21,33-35,94-124`, and
`appendix_b_communication.tex:195-201,398-437`, under
`sources/zip4/manuscript/`. The public row is an existing complete continuous
row, not a replacement discrete table. Private draws here are supplied VALUES;
no distribution or independence assertion is made.

The uninformed set and its activity/held-arm/ID values are fixed at block start.
Every other follower stays true-row unoccupied: ordinary DOWN acceptance is
suppressed. Its initial UP word is the actual codec image of `(0,0,0,0)`.
Saved true-row declarations are external decoder outputs used only in the
boundary flags of the observation trace; they cannot change this block's arms
or truncate its gain. This construction does not implement decoding, launch,
the weight updater, probability laws, or any manuscript theorem.

The recursion is indexed by calendar prefixes. Outside the specified block it
leaves its state unchanged; after the horizon it freezes. `positives` is an
audit log, not an extra policy input. Rectangle exclusion is the literal source
property (ii), visibly supplied only to the quota theorems.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.BootstrapPhysicalBlock

open ConstructorDimensions BootstrapDimensions FiniteBanditModel
open PublicDiscreteDraws ActiveRoundActions RealRewardGridCount
open scoped BigOperators Classical

/-- A genuine complement-arm draw value, without a default arm. -/
abbrev AvoidArm (p : Parameters) (a : Arm p.K) := {c : Arm p.K // c ≠ a}

/-- Exactly the fixed block data and explicit private draw values. Coordinates
for unused uniform draws are latent values, never additional random sharing.
Only followers in `uninformed` have bootstrap activity, held arms and IDs. -/
structure Input (p : Parameters) (s : Fin (n_boot p)) where
  uninformed : Finset (Follower p.m)
  active : {j // j ∈ uninformed} → Bool
  held : {j // j ∈ uninformed} → Arm p.K
  privateId : {j // j ∈ uninformed} → Fin (A_id p)
  ids : CompletePublicTable.IDArray p
  row : CompletePublicTable.CompleteRow p
  target : Arm p.K
  uniform : Player p.m → Fin p.T → Arm p.K
  coordinatorAvoid : Fin p.T → AvoidArm p target
  followerAvoid : (j : {j // j ∈ uninformed}) → Fin p.T → AvoidArm p (held j)
  rewards : Fin p.T → Arm p.K → Fin (D p + 1)

variable {p : Parameters} {s : Fin (n_boot p)}

/-- Slot decoded by the accepted continuous inverse-cumulative sampler. -/
def slot (x : Input p s) (t : Fin p.T) : Slot := slotDraw (x.row.2 t).1

/-- Selected source follower from the true row. -/
def selected (x : Input p s) (t : Fin p.T) : Follower p.m :=
  selectedFollowerDraw p.two_le_m p.m_lt_K (x.row.2 t).1

/-- The full injective tuple from the true row's continuous tuple inputs. -/
def tuple (x : Input p s) (t : Fin p.T) : OrderedTupleSampler.Tuple p.m p.K :=
  OrderedTupleSampler.sample p.two_le_m p.m_lt_K (x.row.2 t).1

/-- One player's genuine row pilot. -/
def pilot (x : Input p s) (t : Fin p.T) (i : Player p.m) : Arm p.K :=
  pilotDraw (K_pos p) i (x.row.2 t).1

/-- The initial ordinary UP record on the accepted codec carrier. The unused
DOWN rate lower bound is zero; UP encoding is independent of that field. -/
def initialUpRecord (p : Parameters) :
    OrdinaryMessageCodec.UpRecord (AffineBatchDecoder.codecParams p 0) :=
  ⟨OrdinaryMessageCodec.upPlaceholder, Or.inl rfl⟩

/-- Actual five-field encoding, flattened using the accepted codec equivalence. -/
def initialUpWord (p : Parameters) : AffineChannelLaw.Word (ContinuousLearningRows.B p) :=
  OrdinaryMessageCodec.wordEquivFlat (AffineBatchDecoder.codecParams p 0)
    (OrdinaryMessageCodec.encodeUp _ (initialUpRecord p))

theorem initialUpWord_eq_zero (p : Parameters) : initialUpWord p = fun _ => 0 := by
  funext i
  change OrdinaryMessageCodec.encodeFive (OrdinaryMessageCodec.fieldWidth p.T (D p))
    0 0 0 0 0 i.divNat i.modNat = 0
  simp [OrdinaryMessageCodec.encodeFive, OrdinaryMessageCodec.fiveField,
    OrdinaryMessageCodec.encodeField]

/-- The initial UP hash uses the UP channel of the selected follower. -/
def initialUpBit (x : Input p s) (t : Fin p.T) (j : Follower p.m) :
    AffineChannelLaw.Bit :=
  AffineChannelLaw.affineHash ((x.row.2 t).2 (1, j)) (initialUpWord p)

theorem initialUpBit_eq_offset (x : Input p s) (t : Fin p.T) (j : Follower p.m) :
    initialUpBit x t j = ((x.row.2 t).2 (1, j)).2 := by
  simp only [initialUpBit, initialUpWord_eq_zero, AffineChannelLaw.affineHash,
    AffineChannelLaw.dotProduct, mul_zero, Finset.sum_const_zero, zero_add]

/-- True-row unoccupied arm rules, including the initial UP SendArm. -/
def unoccupiedAction (x : Input p s) (t : Fin p.T) (j : Follower p.m) : Arm p.K :=
  if slot x t = dataSlot then pilot x t (followerPlayer p.two_le_m j)
  else if slot x t = upSlot ∧ selected x t = j then
    sendArm (initialUpBit x t j) ((tuple x t).val (followerPlayer p.two_le_m j))
      ((tuple x t).val (coordinator p.two_le_m))
  else (tuple x t).val (followerPlayer p.two_le_m j)

/-- Source 07 lines 87-90, on every slot and throughout the entire block. -/
def uninformedAction (x : Input p s) (t : Fin p.T)
    (j : {j // j ∈ x.uninformed}) : Arm p.K :=
  if x.active j = true then
    if x.ids (x.privateId j) t = true then (x.followerAvoid j t).val else x.held j
  else x.uniform (followerPlayer p.two_le_m j.val) t

/-- No pending-declaration or current-observation input occurs in this action. -/
def followerAction (x : Input p s) (t : Fin p.T) (j : Follower p.m) : Arm p.K :=
  if hj : j ∈ x.uninformed then uninformedAction x t ⟨j, hj⟩
  else unoccupiedAction x t j

inductive Mode where
  | discover
  | multicast
  deriving DecidableEq

/-- State before choosing the next arms. `positives` records exactly the
previous DATA coordinator positives while in DISCOVER. -/
structure State (p : Parameters) where
  list : Finset (Fin (A_id p))
  mode : Mode
  positives : Finset (Fin p.T)

/-- Source block-start reset, even if the initial list is already small. -/
def initialState (p : Parameters) : State p := ⟨Finset.univ, .discover, ∅⟩

/-- Literal product of retained forward bits, represented in the naturals.
In particular the product of an empty list is one. -/
def forwardProduct (x : Input p s) (st : State p) (t : Fin p.T) : ℕ :=
  ∏ u ∈ st.list, if x.row.1 u t = true then 1 else 0

theorem forwardProduct_empty (x : Input p s) (st : State p) (t : Fin p.T)
    (h : st.list = ∅) : forwardProduct x st t = 1 := by
  simp only [forwardProduct, h, Finset.prod_empty]

/-- Source 07 lines 75-85: DATA DISCOVER/MULTICAST, DOWN tuple R0,
UP private uniform. A multicast release uses a genuine complement value. -/
def coordinatorAction (x : Input p s) (st : State p) (t : Fin p.T) : Arm p.K :=
  if slot x t = dataSlot then
    if st.mode = .multicast ∧ forwardProduct x st t = 1 then
      (x.coordinatorAvoid t).val else x.target
  else if slot x t = downSlot then (tuple x t).val (coordinator p.two_le_m)
  else x.uniform (coordinator p.two_le_m) t

/-- Simultaneous physical profile; all actions precede all current feedback. -/
def actions (x : Input p s) (st : State p) (t : Fin p.T) : ActionProfile p.m p.K :=
  fun i => if hi : i = coordinator p.two_le_m then coordinatorAction x st t
    else followerAction x t (followerIndex p.two_le_m i hi)

theorem actions_coordinator (x : Input p s) (st : State p) (t : Fin p.T) :
    actions x st t (coordinator p.two_le_m) = coordinatorAction x st t := by
  simp only [actions, dite_true]

theorem actions_follower (x : Input p s) (st : State p) (t : Fin p.T)
    (j : Follower p.m) :
    actions x st t (followerPlayer p.two_le_m j) = followerAction x t j := by
  simp only [actions, dite_eq_right (followerPlayer_ne_coordinator p.two_le_m j),
    followerIndex_followerPlayer]

/-- The accepted physical environment on the explicitly supplied rounded row. -/
def feedback (x : Input p s) (st : State p) (t : Fin p.T) (i : Player p.m) : ℝ :=
  playerFeedback (actions x st t)
    (fun a => realRewardGridValue (D p) (D_pos p) (x.rewards t a)) i

theorem feedback_mem_Icc (x : Input p s) (st : State p) (t : Fin p.T)
    (i : Player p.m) : feedback x st t i ∈ Set.Icc (0 : ℝ) 1 :=
  playerFeedback_mem_Icc_of_bounds _ _
    (fun a => realRewardGridValue_mem_Icc _ _ (x.rewards t a)) i

/-- The integer encoding of this very feedback, including collision zero. -/
def observationIndex (x : Input p s) (st : State p) (t : Fin p.T)
    (i : Player p.m) : Fin (D p + 1) :=
  if collisionFreeFor (actions x st t) i then x.rewards t (actions x st t i)
  else ⟨0, Nat.zero_lt_succ _⟩

theorem observationIndex_value (x : Input p s) (st : State p) (t : Fin p.T)
    (i : Player p.m) :
    realRewardGridValue (D p) (D_pos p) (observationIndex x st t i) =
      feedback x st t i := by
  classical
  by_cases h : collisionFreeFor (actions x st t) i
  · simp only [observationIndex, h, ↓reduceIte, feedback, playerFeedback]
  · simp [observationIndex, h, feedback, playerFeedback, realRewardGridValue]

theorem observationIndex_pos_iff (x : Input p s) (st : State p) (t : Fin p.T)
    (i : Player p.m) :
    0 < (observationIndex x st t i).val ↔ 0 < feedback x st t i := by
  rw [← observationIndex_value]
  change 0 < (observationIndex x st t i).val ↔
    0 < ((observationIndex x st t i).val : ℝ) / (D p : ℝ)
  rw [div_pos_iff_of_pos_right (Nat.cast_pos.mpr (D_pos p)), Nat.cast_pos]

/-- The only event that changes the list. The mode is the pre-choice mode. -/
def discoveryPositive (x : Input p s) (st : State p) (t : Fin p.T) : Prop :=
  t ∈ calendarBlock p s ∧ st.mode = .discover ∧ slot x t = dataSlot ∧
    0 < feedback x st t (coordinator p.two_le_m)

/-- Filter the old list only AFTER a positive; any mode change is for the
next round. MULTICAST therefore freezes the list and the audit log. -/
def step (x : Input p s) (st : State p) (t : Fin p.T) : State p :=
  if discoveryPositive x st t then
    let kept := st.list.filter fun u => x.ids u t = true
    ⟨kept, if kept.card ≤ L0 p then .multicast else .discover, insert t st.positives⟩
  else st

/-- Actual calendar recursion, initialized at this block's start state and
unchanged at earlier/later calendar times outside this block. -/
def run (x : Input p s) : ℕ → State p
  | 0 => initialState p
  | n + 1 => if hn : n < p.T then step x (run x n) ⟨n, hn⟩ else run x n

theorem run_zero (x : Input p s) : run x 0 = initialState p := rfl

theorem run_succ (x : Input p s) (t : Fin p.T) :
    run x (t.val + 1) = step x (run x t.val) t := by
  simp only [run, t.isLt, ↓reduceDIte]

theorem step_of_no_positive (x : Input p s) (st : State p) (t : Fin p.T)
    (h : ¬ discoveryPositive x st t) : step x st t = st := ite_eq_right h

theorem step_multicast (x : Input p s) (st : State p) (t : Fin p.T)
    (h : st.mode = .multicast) : step x st t = st := by
  apply step_of_no_positive
  intro he
  exact Mode.noConfusion (h.symm.trans he.2.1)

theorem step_list_subset (x : Input p s) (st : State p) (t : Fin p.T) :
    (step x st t).list ⊆ st.list := by
  classical
  by_cases h : discoveryPositive x st t
  · simp only [step, h, ↓reduceIte]
    exact Finset.filter_subset _ _
  · rw [step_of_no_positive x st t h]

/-- No observation outside the specified block changes this block's state. -/
theorem step_outside_block (x : Input p s) (st : State p) (t : Fin p.T)
    (ht : t ∉ calendarBlock p s) : step x st t = st :=
  step_of_no_positive x st t (fun h => ht h.1)

/-- In particular earlier calendar rounds cannot alter the block-start reset. -/
theorem run_eq_initial_before_block (x : Input p s) (n : ℕ)
    (hn : n ≤ s.val * B_boot p) : run x n = initialState p := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hi := ih (Nat.le_of_succ_le hn)
      rw [run]
      split
      · next hT =>
          have hnot : (⟨n, hT⟩ : Fin p.T) ∉ calendarBlock p s := by
            intro ht
            have hlo := ((mem_calendarBlock_iff p s _).mp ht).1
            change s.val * B_boot p ≤ n at hlo
            have hn' : n + 1 ≤ s.val * B_boot p := hn
            omega
          rw [step_outside_block x _ _ hnot, hi]
      · exact hi

theorem run_at_block_start (x : Input p s) :
    run x (s.val * B_boot p) = initialState p :=
  run_eq_initial_before_block x _ le_rfl

/-- Collision reasoning, with no list-retention premise. An active held-target
follower would collide with the DISCOVER coordinator whenever its ID bit is zero. -/
theorem id_one_of_discoveryPositive (x : Input p s) (st : State p)
    (t : Fin p.T) (j : {j // j ∈ x.uninformed})
    (ha : x.active j = true) (hz : x.held j = x.target)
    (he : discoveryPositive x st t) : x.ids (x.privateId j) t = true := by
  classical
  by_contra hb
  have hcoord : actions x st t (coordinator p.two_le_m) = x.target := by
    rw [actions_coordinator, coordinatorAction, ite_eq_left he.2.2.1]
    have hdm : Mode.discover ≠ .multicast := by decide
    simp only [he.2.1, hdm, false_and, ↓reduceIte]
  have hfollow : actions x st t (followerPlayer p.two_le_m j.val) = x.target := by
    rw [actions_follower, followerAction, dite_eq_left j.property]
    simp only [uninformedAction, ha, ↓reduceIte, hb, hz]
  have hfree := collisionFreeFor_of_playerFeedback_pos _ _ _ he.2.2.2
  exact hfree (followerPlayer p.two_le_m j.val)
    (followerPlayer_ne_coordinator p.two_le_m j.val) (hfollow.trans hcoord.symm)

theorem step_retains_id (x : Input p s) (st : State p) (t : Fin p.T)
    (j : {j // j ∈ x.uninformed}) (ha : x.active j = true)
    (hz : x.held j = x.target) (hj : x.privateId j ∈ st.list) :
    x.privateId j ∈ (step x st t).list := by
  classical
  by_cases he : discoveryPositive x st t
  · simp only [step, he, ↓reduceIte, Finset.mem_filter]
    exact ⟨hj, id_one_of_discoveryPositive x st t j ha hz he⟩
  · rw [step_of_no_positive x st t he]
    exact hj

/-- The distinguished ID is in EVERY constructed list, with arbitrary other
followers' activity and arbitrary supplied draws and bounded rounded rewards. -/
theorem run_retains_id (x : Input p s) (j : {j // j ∈ x.uninformed})
    (ha : x.active j = true) (hz : x.held j = x.target) (n : ℕ) :
    x.privateId j ∈ (run x n).list := by
  induction n with
  | zero => exact Finset.mem_univ _
  | succ n ih =>
      rw [run]
      split
      · exact step_retains_id x _ _ j ha hz ih
      · exact ih

/-- Every logged positive lies strictly before the current arm choice. -/
theorem run_positive_time_lt (x : Input p s) (n : ℕ) (t : Fin p.T)
    (ht : t ∈ (run x n).positives) : t.val < n := by
  induction n with
  | zero => simp only [run, initialState, Finset.notMem_empty] at ht
  | succ n ih =>
      rw [run] at ht
      split at ht
      · next hn =>
          by_cases he : discoveryPositive x (run x n) ⟨n, hn⟩
          · simp only [step, he, ↓reduceIte, Finset.mem_insert] at ht
            rcases ht with ht | ht
            · subst t
              exact Nat.lt_succ_self n
            · exact Nat.lt_succ_of_lt (ih ht)
          · rw [step_of_no_positive x _ _ he] at ht
            exact Nat.lt_succ_of_lt (ih ht)
      · exact Nat.lt_succ_of_lt (ih ht)

/-- The list is exactly the all-one rows of the physically generated log.
Neither retention nor filtering is assumed. -/
theorem mem_run_list_iff (x : Input p s) (n : ℕ) (u : Fin (A_id p)) :
    u ∈ (run x n).list ↔ ∀ t ∈ (run x n).positives, x.ids u t = true := by
  induction n with
  | zero => simp only [run, initialState, Finset.mem_univ, Finset.notMem_empty,
      IsEmpty.forall_iff, implies_true]
  | succ n ih =>
      rw [run]
      split
      · next hn =>
          by_cases he : discoveryPositive x (run x n) ⟨n, hn⟩
          · simp only [step, he, ↓reduceIte, Finset.mem_filter]
            constructor
            · rintro ⟨hu, hb⟩ t ht
              rcases Finset.mem_insert.mp ht with ht | ht
              · subst t
                exact hb
              · exact ih.mp hu t ht
            · intro h
              exact ⟨ih.mpr (fun t ht => h t (Finset.mem_insert_of_mem ht)),
                h _ (Finset.mem_insert_self _ _)⟩
          · rw [step_of_no_positive x _ _ he]
            exact ih
      · exact ih

/-- Calendar characterization of the log: precisely DATA coordinator positives
while the recursively constructed PRE-CHOICE mode is DISCOVER. -/
theorem mem_run_positives_iff (x : Input p s) (n : ℕ) (t : Fin p.T) :
    t ∈ (run x n).positives ↔
      t.val < n ∧ discoveryPositive x (run x t.val) t := by
  induction n with
  | zero => simp only [run, initialState, Finset.notMem_empty, Nat.not_lt_zero,
      false_and]
  | succ n ih =>
      by_cases hn : n < p.T
      · have hs : run x (n + 1) = step x (run x n) ⟨n, hn⟩ := run_succ x ⟨n, hn⟩
        rw [hs]
        by_cases he : discoveryPositive x (run x n) ⟨n, hn⟩
        · simp only [step, he, ↓reduceIte, Finset.mem_insert, ih]
          constructor
          · rintro (ht | ⟨ht, hp⟩)
            · subst t
              exact ⟨Nat.lt_succ_self _, he⟩
            · exact ⟨Nat.lt_succ_of_lt ht, hp⟩
          · rintro ⟨ht, hp⟩
            by_cases htn : t.val = n
            · exact Or.inl (Fin.ext htn)
            · exact Or.inr ⟨by omega, hp⟩
        · rw [step_of_no_positive x _ _ he, ih]
          constructor
          · rintro ⟨ht, hp⟩
            exact ⟨Nat.lt_succ_of_lt ht, hp⟩
          · rintro ⟨ht, hp⟩
            have htn : t.val ≠ n := by
              intro htn
              have hteq : t = ⟨n, hn⟩ := Fin.ext htn
              subst t
              exact he hp
            exact ⟨by omega, hp⟩
      · simp only [run, hn, ↓reduceDIte, ih]
        have ht := t.isLt
        constructor
        · rintro ⟨hlt, hp⟩
          exact ⟨Nat.lt_succ_of_lt hlt, hp⟩
        · rintro ⟨_, hp⟩
          exact ⟨by omega, hp⟩

/-- A literal set of the physical DATA positives over the whole calendar block. -/
def discoveryPositiveRounds (x : Input p s) : Finset (Fin p.T) :=
  (calendarBlock p s).filter fun t =>
    (run x t.val).mode = .discover ∧ slot x t = dataSlot ∧
      0 < feedback x (run x t.val) t (coordinator p.two_le_m)

theorem run_positives_eq_physical_rounds (x : Input p s) :
    (run x p.T).positives = discoveryPositiveRounds x := by
  ext t
  rw [mem_run_positives_iff]
  simp only [discoveryPositiveRounds, Finset.mem_filter, discoveryPositive,
    t.isLt, true_and]

/-- Prefix version of the physical-log equality, for a quota attained partway
through the block. Prefixes are calendar prefixes, not DATA-only clocks. -/
theorem run_positives_eq_physical_prefix (x : Input p s) (n : ℕ) :
    (run x n).positives = (discoveryPositiveRounds x).filter (fun t => t.val < n) := by
  ext t
  simp only [mem_run_positives_iff, discoveryPositiveRounds, Finset.mem_filter,
    discoveryPositive, and_comm]

/-- Literal source rectangle-exclusion PROPERTY (ii),
`appendix_b_communication.tex:195-201`: every set of exactly `6*b_N`
distinct calendar times has fewer than `L0` all-one ID rows. -/
def rectangle_exclusion (ids : CompletePublicTable.IDArray p) : Prop :=
  ∀ times : Finset (Fin p.T), times.card = 6 * b_N p →
    ((Finset.univ : Finset (Fin (A_id p))).filter
      fun u => ∀ t ∈ times, ids u t = true).card < L0 p

/-- The exact source property applies to a constructed prefix's list. -/
theorem run_list_card_lt_of_quota (x : Input p s)
    (hrect : rectangle_exclusion x.ids) (n : ℕ)
    (hq : (run x n).positives.card = 6 * b_N p) :
    (run x n).list.card < L0 p := by
  have heq : (run x n).list = (Finset.univ.filter
      fun u => ∀ t ∈ (run x n).positives, x.ids u t = true) := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_run_list_iff]
  rw [heq]
  exact hrect _ hq

/-- A post-round multicast state really has a list of size at most `L0`. -/
theorem run_multicast_list_card_le (x : Input p s) (n : ℕ)
    (hm : (run x n).mode = .multicast) : (run x n).list.card ≤ L0 p := by
  induction n with
  | zero => exact Mode.noConfusion hm
  | succ n ih =>
      by_cases hn : n < p.T
      · rw [run_succ x ⟨n, hn⟩] at hm ⊢
        by_cases he : discoveryPositive x (run x n) ⟨n, hn⟩
        · simp only [step, he, ↓reduceIte] at hm ⊢
          split at hm
          · assumption
          · exact Mode.noConfusion hm
        · rw [step_of_no_positive x _ _ he] at hm ⊢
          exact ih hm
      · rw [run, dite_eq_right hn] at hm ⊢
        exact ih hm

/-- Mode persistence and complete list/log freezing are consequences of the
recursion. No decoder output during the block can change them. -/
theorem run_eq_of_multicast (x : Input p s) (n k : ℕ)
    (hm : (run x n).mode = .multicast) : run x (n + k) = run x n := by
  induction k with
  | zero => rw [Nat.add_zero]
  | succ k ih =>
      rw [Nat.add_succ, run]
      split
      · rw [ih, step_multicast x _ _ hm]
      · exact ih

/-- Quota invariant: there are never more than `6*b_N` positives; while still
in DISCOVER the count is strictly smaller. The only external mathematical input
is the explicitly expanded source rectangle property. -/
theorem run_discovery_quota (x : Input p s) (hrect : rectangle_exclusion x.ids)
    (n : ℕ) :
    (run x n).positives.card ≤ 6 * b_N p ∧
      ((run x n).mode = .discover → (run x n).positives.card < 6 * b_N p) := by
  induction n with
  | zero =>
      change 0 ≤ 6 * b_N p ∧ (Mode.discover = .discover → 0 < 6 * b_N p)
      exact ⟨Nat.zero_le _, fun _ => Nat.mul_pos (by decide) (b_N_pos p)⟩
  | succ n ih =>
      by_cases hn : n < p.T
      · have hs : run x (n + 1) = step x (run x n) ⟨n, hn⟩ := run_succ x ⟨n, hn⟩
        by_cases he : discoveryPositive x (run x n) ⟨n, hn⟩
        · have hnew : (⟨n, hn⟩ : Fin p.T) ∉ (run x n).positives := by
            intro ht
            exact (Nat.lt_irrefl n) (run_positive_time_lt x n _ ht)
          have hc : (run x (n + 1)).positives.card = (run x n).positives.card + 1 := by
            rw [hs]
            simp only [step, he, ↓reduceIte, Finset.card_insert_of_notMem hnew]
          have hold := ih.2 he.2.1
          have hle : (run x (n + 1)).positives.card ≤ 6 * b_N p := by omega
          refine ⟨hle, ?_⟩
          intro hm
          by_contra hlt
          have hq : (run x (n + 1)).positives.card = 6 * b_N p := by omega
          have hsmall := (run_list_card_lt_of_quota x hrect (n + 1) hq).le
          rw [hs] at hm hsmall
          simp only [step, he, ↓reduceIte] at hm hsmall
          rw [ite_eq_left hsmall] at hm
          exact Mode.noConfusion hm
        · rw [hs, step_of_no_positive x _ _ he]
          exact ih
      · simpa only [run, hn, ↓reduceDIte] using ih

/-- Attaining the quota has already changed the mode for the next arm choice.
No switching hypothesis appears here. -/
theorem run_multicast_of_quota (x : Input p s) (hrect : rectangle_exclusion x.ids)
    (n : ℕ) (hq : (run x n).positives.card = 6 * b_N p) :
    (run x n).mode = .multicast := by
  have h := (run_discovery_quota x hrect n).2
  cases hm : (run x n).mode with
  | discover => exact False.elim ((Nat.ne_of_lt (h hm)) hq)
  | multicast => rfl

/-- The requested next-round statement, including the final boundary state
when the quota is attained on the last calendar round. -/
theorem switch_next_round_of_quota (x : Input p s)
    (hrect : rectangle_exclusion x.ids) (t : Fin p.T)
    (hq : (run x (t.val + 1)).positives.card = 6 * b_N p) :
    (run x (t.val + 1)).mode = .multicast ∧
      (run x (t.val + 1)).list.card ≤ L0 p := by
  have hm := run_multicast_of_quota x hrect _ hq
  exact ⟨hm, run_multicast_list_card_le x _ hm⟩

/-- At most `6*b_N` actual DATA coordinator positives during DISCOVER in this
block, proved from the physical recursion and PROPERTY (ii). -/
theorem discoveryPositiveRounds_card_le (x : Input p s)
    (hrect : rectangle_exclusion x.ids) :
    (discoveryPositiveRounds x).card ≤ 6 * b_N p := by
  rw [← run_positives_eq_physical_rounds]
  exact (run_discovery_quota x hrect p.T).1

/-- If the physical DATA-positive prefix has attained the quota at the end of
round `t`, the next pre-choice mode is MULTICAST and its list is small. -/
theorem switch_of_physical_positive_quota (x : Input p s)
    (hrect : rectangle_exclusion x.ids) (t : Fin p.T)
    (hq : ((discoveryPositiveRounds x).filter
      (fun r => r.val < t.val + 1)).card = 6 * b_N p) :
    (run x (t.val + 1)).mode = .multicast ∧
      (run x (t.val + 1)).list.card ≤ L0 p := by
  apply switch_next_round_of_quota x hrect t
  rw [run_positives_eq_physical_prefix]
  exact hq

/-- All slots are included in the physical stay count; no saved-declaration
cutoff and no DATA restriction occurs here (source 07 lines 30-31,92-94). -/
def physicalStayRounds (x : Input p s) (j : {j // j ∈ x.uninformed}) :
    Finset (Fin p.T) :=
  (calendarBlock p s).filter fun t => x.ids (x.privateId j) t = false ∧
    0 < feedback x (run x t.val) t (followerPlayer p.two_le_m j.val)

/-- Actual source block gain, zero on inactive blocks. -/
def physicalStayGain (x : Input p s) (j : {j // j ∈ x.uninformed}) : ℕ :=
  if x.active j = true then (physicalStayRounds x j).card else 0

/-- Construct the accepted trace on THIS block from its physical feedbacks.
Other blocks have zero observations and are disabled. `savedAt` supplies only
true-row candidate-test outputs; this module makes no decoding claim about it.
The boundary launch flag likewise has no effect on arms or observations here. -/
def observationTrace (x : Input p s) (j : {j // j ∈ x.uninformed})
    (savedAt : Fin p.T → Bool) (launchAtBoundary : Bool) :
    BootstrapBlockConstruction.ExplicitTrace p where
  idBits := x.ids
  observation t := if t ∈ calendarBlock p s then
    observationIndex x (run x t.val) t (followerPlayer p.two_le_m j.val)
    else ⟨0, Nat.zero_lt_succ _⟩
  active r := decide (r = s) && x.active j
  heldArm _ := x.held j
  privateId _ := x.privateId j
  savedDeclaration r := decide (r = s ∧ ∃ t ∈ calendarBlock p s, savedAt t = true)
  coordinatorLaunch r := decide (r = s) && launchAtBoundary

/-- Saving at any point records a declaration for this block's BOUNDARY. It
does not feed a new status back into the round-action recursion. -/
theorem observationTrace_savedDeclaration (x : Input p s)
    (j : {j // j ∈ x.uninformed}) (savedAt : Fin p.T → Bool)
    (launchAtBoundary : Bool) :
    (observationTrace x j savedAt launchAtBoundary).savedDeclaration s = true ↔
      ∃ t ∈ calendarBlock p s, savedAt t = true := by
  simp only [observationTrace, true_and, decide_eq_true_eq]

/-- The constructed trace observation is exactly the physical feedback on
every round of this calendar block, not an assumed trace equality. -/
theorem observationTrace_value (x : Input p s) (j : {j // j ∈ x.uninformed})
    (savedAt : Fin p.T → Bool) (launchAtBoundary : Bool) (t : Fin p.T)
    (ht : t ∈ calendarBlock p s) :
    realRewardGridValue (D p) (D_pos p)
        ((observationTrace x j savedAt launchAtBoundary).observation t) =
      feedback x (run x t.val) t (followerPlayer p.two_le_m j.val) := by
  simp only [observationTrace, ht, ↓reduceIte]
  exact observationIndex_value x _ _ _

/-- The accepted raw calendar gain is the constructed physical all-slot count. -/
theorem calendarBlockGain_eq_physical_count (x : Input p s)
    (j : {j // j ∈ x.uninformed}) (savedAt : Fin p.T → Bool)
    (launchAtBoundary : Bool) :
    BootstrapBlockConstruction.calendarBlockGain
        (observationTrace x j savedAt launchAtBoundary) s =
      (physicalStayRounds x j).card := by
  unfold BootstrapBlockConstruction.calendarBlockGain
    BootstrapBlockConstruction.positiveStayRounds physicalStayRounds
  congr 1
  apply Finset.filter_congr
  intro t ht
  simp only [observationTrace, ht, ↓reduceIte, observationIndex_pos_iff]

/-- All earlier blocks in this one-block trace are disabled and have no stop
events. The current block's pending declaration/launch is strictly excluded. -/
theorem observationTrace_aliveBefore (x : Input p s)
    (j : {j // j ∈ x.uninformed}) (savedAt : Fin p.T → Bool)
    (launchAtBoundary : Bool) :
    BootstrapBlockConstruction.aliveBefore
      (observationTrace x j savedAt launchAtBoundary) s = true := by
  apply decide_eq_true_eq.mpr
  intro r hrs
  have hne : r ≠ s := by
    intro h
    subst r
    exact (Nat.lt_irrefl _) hrs
  simp [BootstrapBlockConstruction.stopEvent, observationTrace, hne]

theorem observationTrace_blockEnabled (x : Input p s)
    (j : {j // j ∈ x.uninformed}) (savedAt : Fin p.T → Bool)
    (launchAtBoundary : Bool) :
    BootstrapBlockConstruction.blockEnabled
      (observationTrace x j savedAt launchAtBoundary) s = x.active j := by
  rw [BootstrapBlockConstruction.blockEnabled, observationTrace_aliveBefore,
    Bool.and_true]
  simp only [observationTrace, decide_true, Bool.true_and]

/-- The accepted gain updater receives precisely the full physical source gain,
including non-DATA rounds and observations after saving a declaration. -/
theorem effectiveCalendarBlockGain_eq_physicalStayGain (x : Input p s)
    (j : {j // j ∈ x.uninformed}) (savedAt : Fin p.T → Bool)
    (launchAtBoundary : Bool) :
    BootstrapBlockConstruction.effectiveCalendarBlockGain
        (observationTrace x j savedAt launchAtBoundary) s = physicalStayGain x j := by
  simp only [BootstrapBlockConstruction.effectiveCalendarBlockGain,
    observationTrace_blockEnabled, calendarBlockGain_eq_physical_count, physicalStayGain]

/-- Direct interface to the existing weight-updater input; no new updater. -/
theorem blockInput_effectiveGain_eq_physicalStayGain (x : Input p s)
    (j : {j // j ∈ x.uninformed}) (savedAt : Fin p.T → Bool)
    (launchAtBoundary : Bool) :
    BootstrapWeightPotential.effectiveGain
        (BootstrapBlockConstruction.blockInput
          (observationTrace x j savedAt launchAtBoundary) s) = physicalStayGain x j := by
  rw [← BootstrapBlockConstruction.effectiveCalendarBlockGain_eq_effectiveGain]
  exact effectiveCalendarBlockGain_eq_physicalStayGain x j savedAt launchAtBoundary

/-- Changing when a declaration is saved cannot stop this block's gain count,
even if the boundary launch flag also changes. -/
theorem gain_independent_of_saved_declaration (x : Input p s)
    (j : {j // j ∈ x.uninformed}) (saved₁ saved₂ : Fin p.T → Bool)
    (launch₁ launch₂ : Bool) :
    BootstrapBlockConstruction.effectiveCalendarBlockGain
        (observationTrace x j saved₁ launch₁) s =
      BootstrapBlockConstruction.effectiveCalendarBlockGain
        (observationTrace x j saved₂ launch₂) s := by
  rw [effectiveCalendarBlockGain_eq_physicalStayGain,
    effectiveCalendarBlockGain_eq_physicalStayGain]

/-- The distinction between observations before and after saving is an exact
partition, with the save round itself in the latter part. -/
theorem physicalStayGain_cutoff (x : Input p s) (j : {j // j ∈ x.uninformed})
    (ha : x.active j = true) (cutoff : Fin p.T) :
    physicalStayGain x j =
      ((physicalStayRounds x j).filter fun t => t.val < cutoff.val).card +
        ((physicalStayRounds x j).filter fun t => cutoff.val ≤ t.val).card := by
  rw [physicalStayGain, ite_eq_left ha]
  have h := Finset.card_filter_add_card_filter_not (s := physicalStayRounds x j)
    (p := fun t => t.val < cutoff.val)
  simpa only [not_lt] using h.symm

/-- An active uninformed follower holds its arm on ID-zero rounds of ANY slot. -/
theorem uninformedAction_stay (x : Input p s) (t : Fin p.T)
    (j : {j // j ∈ x.uninformed}) (ha : x.active j = true)
    (hb : x.ids (x.privateId j) t = false) : uninformedAction x t j = x.held j := by
  simp only [uninformedAction, ha, ↓reduceIte, hb, Bool.false_eq_true, ↓reduceIte]

theorem uninformedAction_avoid (x : Input p s) (t : Fin p.T)
    (j : {j // j ∈ x.uninformed}) (ha : x.active j = true)
    (hb : x.ids (x.privateId j) t = true) : uninformedAction x t j ≠ x.held j := by
  simpa only [uninformedAction, ha, hb, ↓reduceIte] using (x.followerAvoid j t).property

theorem uninformedAction_inactive (x : Input p s) (t : Fin p.T)
    (j : {j // j ∈ x.uninformed}) (ha : x.active j = false) :
    uninformedAction x t j = x.uniform (followerPlayer p.two_le_m j.val) t := by
  simp only [uninformedAction, ha, Bool.false_eq_true, ↓reduceIte]

/-- Informed followers' DOWN action is literally their tuple arm. -/
theorem unoccupiedAction_down (x : Input p s) (t : Fin p.T) (j : Follower p.m)
    (ht : slot x t = downSlot) :
    unoccupiedAction x t j = (tuple x t).val (followerPlayer p.two_le_m j) := by
  have hnd : downSlot ≠ dataSlot := by decide
  have hnu : downSlot ≠ upSlot := by decide
  simp only [unoccupiedAction, ht, hnd, hnu, false_and, ↓reduceIte]

/-- Informed selected UP sends the actual initial record, not a uniform arm. -/
theorem unoccupiedAction_selected_up (x : Input p s) (t : Fin p.T)
    (ht : slot x t = upSlot) :
    unoccupiedAction x t (selected x t) =
      sendArm (((x.row.2 t).2 (1, selected x t)).2)
        ((tuple x t).val (followerPlayer p.two_le_m (selected x t)))
        ((tuple x t).val (coordinator p.two_le_m)) := by
  have hnd : upSlot ≠ dataSlot := by decide
  simp only [unoccupiedAction, ht, hnd, ↓reduceIte, and_self, initialUpBit_eq_offset]

theorem coordinatorAction_discover_data (x : Input p s) (st : State p)
    (t : Fin p.T) (hm : st.mode = .discover) (ht : slot x t = dataSlot) :
    coordinatorAction x st t = x.target := by
  have hdm : Mode.discover ≠ .multicast := by decide
  simp only [coordinatorAction, ht, hm, hdm, false_and, ↓reduceIte]

/-- The conditional release formula retains the product over the ENTIRE list. -/
theorem coordinatorAction_multicast_data (x : Input p s) (st : State p)
    (t : Fin p.T) (hm : st.mode = .multicast) (ht : slot x t = dataSlot) :
    coordinatorAction x st t =
      if forwardProduct x st t = 1 then (x.coordinatorAvoid t).val else x.target := by
  simp only [coordinatorAction, ht, hm, true_and, ↓reduceIte]

theorem coordinatorAction_down (x : Input p s) (st : State p) (t : Fin p.T)
    (ht : slot x t = downSlot) :
    coordinatorAction x st t = (tuple x t).val (coordinator p.two_le_m) := by
  have hnd : downSlot ≠ dataSlot := by decide
  simp only [coordinatorAction, ht, hnd, ↓reduceIte]

theorem coordinatorAction_up (x : Input p s) (st : State p) (t : Fin p.T)
    (ht : slot x t = upSlot) :
    coordinatorAction x st t = x.uniform (coordinator p.two_le_m) t := by
  have hnd : upSlot ≠ dataSlot := by decide
  have hnu : upSlot ≠ downSlot := by decide
  simp only [coordinatorAction, ht, hnd, hnu, ↓reduceIte]

end Bandits.Support.BootstrapPhysicalBlock

end
