module

public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fin.Tuple.Basic

import Mathlib.Tactic.Ring

/-!
# Finite multiplayer bandit environment

The source model is `sources/zip4/manuscript/01_introduction.tex:19-36`:
arms and rounds are indexed by `Fin`, rewards are arbitrary reals in `[0,1]`,
and a player receives its chosen reward precisely when no other player chose
that arm. The pathwise reward and fixed-set comparator use the model in
`sources/zip4/manuscript/01_introduction.tex:30-36`; the real-reward comparison
is also used at `sources/zip4/manuscript/08_main_theorem.tex:163-174`.

The rollout below is deterministic after its public data and each player's
private input are fixed. Its policy interface sees only that player's history.
This module does not assign probability measures to private inputs or claim
measurability or an implementation of the manuscript protocol.
-/

@[expose] public section

namespace Bandits.Support.FiniteBanditModel

/-- The arm set `[K]`, represented by `Fin K` with source label `val + 1`. -/
abbrev Arm (K : ℕ) := Fin K

/-- The player set `{0, ..., m - 1}`, represented by `Fin m`. -/
abbrev Player (m : ℕ) := Fin m

/-- A source arm label in `[K]`, using the manuscript's one-based convention. -/
def armSourceLabel {K : ℕ} (a : Arm K) : ℕ := a.val + 1

/-- The source arm label ranges from `1` through `K`. -/
theorem armSourceLabel_bounds {K : ℕ} (a : Arm K) :
    1 ≤ armSourceLabel a ∧ armSourceLabel a ≤ K := by
  constructor
  · simp [armSourceLabel]
  · simpa [armSourceLabel] using Nat.succ_le_of_lt a.isLt

/-- A source player label in `{0, ..., m - 1}`. -/
def playerSourceLabel {m : ℕ} (i : Player m) : ℕ := i.val

/-- The source player label is between `0` and `m - 1`. -/
theorem playerSourceLabel_lt {m : ℕ} (i : Player m) : playerSourceLabel i < m := i.isLt

/-- A source round label in `[T]`, using the manuscript's one-based convention. -/
def roundSourceLabel {T : ℕ} (t : Fin T) : ℕ := t.val + 1

/-- The source round label ranges from `1` through `T`. -/
theorem roundSourceLabel_bounds {T : ℕ} (t : Fin T) :
    1 ≤ roundSourceLabel t ∧ roundSourceLabel t ≤ T := by
  constructor
  · simp [roundSourceLabel]
  · simpa [roundSourceLabel] using Nat.succ_le_of_lt t.isLt

/-- A real reward table on the finite arm and round sets, with every entry in `[0,1]`. -/
structure RewardMatrix (T K : ℕ) where
  reward : Fin T → Arm K → ℝ
  reward_mem_Icc : ∀ t a, reward t a ∈ Set.Icc (0 : ℝ) 1

/-- A simultaneous profile of one arm choice for each player. -/
abbrev ActionProfile (m K : ℕ) := Player m → Arm K

/-- The chosen arm is unoccupied by every other player. -/
def collisionFreeFor {m K : ℕ} (actions : ActionProfile m K) (i : Player m) : Prop :=
  ∀ j, j ≠ i → actions j ≠ actions i

/-- The scalar feedback received by player `i` in one round. -/
def playerFeedback {m K : ℕ} (actions : ActionProfile m K) (rewards : Arm K → ℝ)
    (i : Player m) : ℝ :=
  by
    letI : Decidable (collisionFreeFor actions i) := by
      unfold collisionFreeFor
      infer_instance
    exact if collisionFreeFor actions i then rewards (actions i) else 0

/-- Feedback against an arbitrary reward row is in `[0,1]` when that row is bounded. -/
theorem playerFeedback_mem_Icc_of_bounds {m K : ℕ} (actions : ActionProfile m K)
    (rewards : Arm K → ℝ) (hrewards : ∀ a, rewards a ∈ Set.Icc (0 : ℝ) 1)
    (i : Player m) :
    playerFeedback actions rewards i ∈ Set.Icc (0 : ℝ) 1 := by
  classical
  by_cases h : collisionFreeFor actions i
  · simpa [playerFeedback, h] using hrewards (actions i)
  · simp [playerFeedback, h]

/-- Feedback on a row of a bounded reward matrix is in `[0,1]`. -/
theorem rewardMatrixFeedback_mem_Icc {m K T : ℕ} (actions : ActionProfile m K)
    (rewards : RewardMatrix T K) (t : Fin T) (i : Player m) :
    playerFeedback actions (rewards.reward t) i ∈ Set.Icc (0 : ℝ) 1 :=
  playerFeedback_mem_Icc_of_bounds actions (rewards.reward t) (rewards.reward_mem_Icc t) i

/-- A positive observation rules out every collision involving that player. -/
theorem collisionFreeFor_of_playerFeedback_pos {m K : ℕ}
    (actions : ActionProfile m K) (rewards : Arm K → ℝ) (i : Player m)
    (hpos : 0 < playerFeedback actions rewards i) : collisionFreeFor actions i := by
  classical
  by_contra hcollision
  have hzero : playerFeedback actions rewards i = 0 := by
    simp [playerFeedback, hcollision]
  rw [hzero] at hpos
  exact (lt_irrefl 0) hpos

/-- If the profile is injective, total feedback is exactly the reward on its image arms. -/
theorem feedback_sum_eq_image_reward_of_injective {m K : ℕ}
    (actions : ActionProfile m K) (rewards : Arm K → ℝ)
    (hinj : Function.Injective actions) :
    (∑ i : Player m, playerFeedback actions rewards i) =
      ∑ a ∈ (Finset.univ : Finset (Player m)).image actions, rewards a := by
  classical
  calc
    (∑ i : Player m, playerFeedback actions rewards i) =
        ∑ i : Player m, rewards (actions i) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hd : collisionFreeFor actions i := by
        intro j hji hsame
        exact hji (hinj hsame)
      simp [playerFeedback, hd]
    _ = ∑ a ∈ (Finset.univ : Finset (Player m)).image actions, rewards a := by
      rw [Finset.sum_image (fun i hi j hj hij => hinj hij)]

/-- A length-`t` local history contains only this player's past actions and scalar observations. -/
abbrev LocalHistory (K t : ℕ) := Fin t → (Arm K × ℝ)

/-- A player's local decision function receives its identity, public data, local history,
and private input. It has no argument for another player's information or for the reward table. -/
abbrev PlayerLocalDecision (m K : ℕ) (PublicData PrivateInput : Type*) :=
  (i : Player m) → (t : ℕ) → PublicData → LocalHistory K t → PrivateInput → Arm K

/-- A run prefix records the simultaneous actions and scalar feedback in its first `t` rounds. -/
structure RunPrefix (m K t : ℕ) where
  action : Fin t → ActionProfile m K
  feedback : Fin t → Player m → ℝ

/-- Extract one player's local history from a run prefix. -/
def localHistoryOfRun {m K t : ℕ} (run : RunPrefix m K t) (i : Player m) : LocalHistory K t :=
  fun s => (run.action s i, run.feedback s i)

/-- Recursively construct the first `t` rounds from empty histories.

At step `t + 1`, every player's action is computed from the preceding prefix's
derived local history, then feedback is computed from that action profile and
the reward row for the next round.
-/
def deterministicRolloutPrefix {m K T : ℕ} {PublicData PrivateInput : Type*}
    (decide : PlayerLocalDecision m K PublicData PrivateInput) (publicData : PublicData)
    (privateInput : Player m → PrivateInput) (rewards : RewardMatrix T K) :
    (t : ℕ) → t ≤ T → RunPrefix m K t
  | 0, _ => ⟨Fin.elim0, Fin.elim0⟩
  | t + 1, ht =>
      let previous := deterministicRolloutPrefix decide publicData privateInput rewards t
        (Nat.le_of_succ_le ht)
      let currentActions : ActionProfile m K := fun i =>
        decide i t publicData (localHistoryOfRun previous i) (privateInput i)
      let currentFeedback : Player m → ℝ := fun i =>
        playerFeedback currentActions
          (rewards.reward (Fin.castLE ht (Fin.last t))) i
      ⟨Fin.snoc previous.action currentActions,
        Fin.snoc previous.feedback currentFeedback⟩

/-- The finite deterministic rollout on the complete `T`-round reward matrix. -/
def deterministicRollout {m K T : ℕ} {PublicData PrivateInput : Type*}
    (decide : PlayerLocalDecision m K PublicData PrivateInput) (publicData : PublicData)
    (privateInput : Player m → PrivateInput) (rewards : RewardMatrix T K) : RunPrefix m K T :=
  deterministicRolloutPrefix decide publicData privateInput rewards T (Nat.le_refl T)

/-- A deterministic rollout exists for every fixed public datum, private-input profile,
and bounded reward matrix. -/
theorem deterministicRollout_exists {m K T : ℕ} {PublicData PrivateInput : Type*}
    (decide : PlayerLocalDecision m K PublicData PrivateInput) (publicData : PublicData)
    (privateInput : Player m → PrivateInput) (rewards : RewardMatrix T K) :
    ∃ run : RunPrefix m K T,
      run = deterministicRollout decide publicData privateInput rewards :=
  ⟨deterministicRollout decide publicData privateInput rewards, rfl⟩

/-- Earlier actions in a one-step-extended rollout are the previous run's actions. -/
theorem deterministicRolloutPrefix_action_castSucc {m K T : ℕ}
    {PublicData PrivateInput : Type*}
    (decide : PlayerLocalDecision m K PublicData PrivateInput) (publicData : PublicData)
    (privateInput : Player m → PrivateInput) (rewards : RewardMatrix T K)
    (t : ℕ) (ht : t + 1 ≤ T) (s : Fin t) (i : Player m) :
    (deterministicRolloutPrefix decide publicData privateInput rewards (t + 1) ht).action
        s.castSucc i =
      (deterministicRolloutPrefix decide publicData privateInput rewards t
        (Nat.le_of_succ_le ht)).action s i := by
  simp only [deterministicRolloutPrefix, Fin.snoc_castSucc]

/-- Earlier feedback in a one-step-extended rollout is the previous run's feedback. -/
theorem deterministicRolloutPrefix_feedback_castSucc {m K T : ℕ}
    {PublicData PrivateInput : Type*}
    (decide : PlayerLocalDecision m K PublicData PrivateInput) (publicData : PublicData)
    (privateInput : Player m → PrivateInput) (rewards : RewardMatrix T K)
    (t : ℕ) (ht : t + 1 ≤ T) (s : Fin t) (i : Player m) :
    (deterministicRolloutPrefix decide publicData privateInput rewards (t + 1) ht).feedback
        s.castSucc i =
      (deterministicRolloutPrefix decide publicData privateInput rewards t
        (Nat.le_of_succ_le ht)).feedback s i := by
  simp only [deterministicRolloutPrefix, Fin.snoc_castSucc]

/-- The new action is chosen from the previous prefix's derived local history. -/
theorem deterministicRolloutPrefix_action_last {m K T : ℕ}
    {PublicData PrivateInput : Type*}
    (decide : PlayerLocalDecision m K PublicData PrivateInput) (publicData : PublicData)
    (privateInput : Player m → PrivateInput) (rewards : RewardMatrix T K)
    (t : ℕ) (ht : t + 1 ≤ T) (i : Player m) :
    (deterministicRolloutPrefix decide publicData privateInput rewards (t + 1) ht).action
        (Fin.last t) i =
      decide i t publicData
        (localHistoryOfRun
          (deterministicRolloutPrefix decide publicData privateInput rewards t
            (Nat.le_of_succ_le ht)) i)
        (privateInput i) := by
  simp only [deterministicRolloutPrefix, Fin.snoc_last]

/-- The new observation is the exact collision feedback for the new action profile. -/
theorem deterministicRolloutPrefix_feedback_last {m K T : ℕ}
    {PublicData PrivateInput : Type*}
    (decide : PlayerLocalDecision m K PublicData PrivateInput) (publicData : PublicData)
    (privateInput : Player m → PrivateInput) (rewards : RewardMatrix T K)
    (t : ℕ) (ht : t + 1 ≤ T) (i : Player m) :
    (deterministicRolloutPrefix decide publicData privateInput rewards (t + 1) ht).feedback
        (Fin.last t) i =
      playerFeedback
        (fun j => decide j t publicData
          (localHistoryOfRun
            (deterministicRolloutPrefix decide publicData privateInput rewards t
              (Nat.le_of_succ_le ht)) j)
          (privateInput j))
        (rewards.reward (Fin.castLE ht (Fin.last t))) i := by
  simp only [deterministicRolloutPrefix, Fin.snoc_last]

/-- Every observation in every recursively constructed prefix obeys the reward bounds. -/
theorem deterministicRolloutPrefix_feedback_mem_Icc {m K T : ℕ}
    {PublicData PrivateInput : Type*}
    (decide : PlayerLocalDecision m K PublicData PrivateInput) (publicData : PublicData)
    (privateInput : Player m → PrivateInput) (rewards : RewardMatrix T K) :
    ∀ (t : ℕ) (ht : t ≤ T) (s : Fin t) (i : Player m),
      (deterministicRolloutPrefix decide publicData privateInput rewards t ht).feedback s i ∈
        Set.Icc (0 : ℝ) 1 := by
  intro t
  induction t with
  | zero =>
      intro ht s i
      exact Fin.elim0 s
  | succ t ih =>
      intro ht s i
      cases s using Fin.lastCases with
      | last =>
          rw [deterministicRolloutPrefix_feedback_last]
          exact playerFeedback_mem_Icc_of_bounds _ _
            (fun a => rewards.reward_mem_Icc (Fin.castLE ht (Fin.last t)) a) i
      | cast s =>
          rw [deterministicRolloutPrefix_feedback_castSucc]
          exact ih (Nat.le_of_succ_le ht) s i

/-- The observations in a complete rollout obey the reward bounds. -/
theorem deterministicRollout_feedback_mem_Icc {m K T : ℕ}
    {PublicData PrivateInput : Type*}
    (decide : PlayerLocalDecision m K PublicData PrivateInput) (publicData : PublicData)
    (privateInput : Player m → PrivateInput) (rewards : RewardMatrix T K)
    (t : Fin T) (i : Player m) :
    (deterministicRollout decide publicData privateInput rewards).feedback t i ∈
      Set.Icc (0 : ℝ) 1 := by
  exact deterministicRolloutPrefix_feedback_mem_Icc decide publicData privateInput rewards
    T (Nat.le_refl T) t i

/-- Pathwise cumulative feedback, equal to the total reward actually received over the run. -/
def pathwiseCumulativeReward {m K T : ℕ} (run : RunPrefix m K T) : ℝ :=
  ∑ t : Fin T, ∑ i : Player m, run.feedback t i

/-- A run with `[0,1]` observations has total reward in `[0,mT]`. -/
theorem pathwiseCumulativeReward_mem_Icc {m K T : ℕ} (run : RunPrefix m K T)
    (hfeedback : ∀ t i, run.feedback t i ∈ Set.Icc (0 : ℝ) 1) :
    pathwiseCumulativeReward run ∈ Set.Icc (0 : ℝ) ((m : ℝ) * (T : ℝ)) := by
  constructor
  · unfold pathwiseCumulativeReward
    apply Finset.sum_nonneg
    intro t ht
    apply Finset.sum_nonneg
    intro i hi
    exact (hfeedback t i).1
  · unfold pathwiseCumulativeReward
    calc
      (∑ t : Fin T, ∑ i : Player m, run.feedback t i) ≤
          ∑ t : Fin T, ∑ i : Player m, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro t ht
        apply Finset.sum_le_sum
        intro i hi
        exact (hfeedback t i).2
      _ = (T : ℝ) * (m : ℝ) := by simp
      _ = (m : ℝ) * (T : ℝ) := by ring

/-- The pathwise cumulative reward of the recursive rollout is in `[0,mT]`. -/
theorem deterministicRollout_pathwiseCumulativeReward_mem_Icc {m K T : ℕ}
    {PublicData PrivateInput : Type*}
    (decide : PlayerLocalDecision m K PublicData PrivateInput) (publicData : PublicData)
    (privateInput : Player m → PrivateInput) (rewards : RewardMatrix T K) :
    pathwiseCumulativeReward
      (deterministicRollout decide publicData privateInput rewards) ∈
        Set.Icc (0 : ℝ) ((m : ℝ) * (T : ℝ)) := by
  apply pathwiseCumulativeReward_mem_Icc
  exact deterministicRollout_feedback_mem_Icc decide publicData privateInput rewards

/-- A nonempty fixed `m`-set of arms, represented by its literal finite subset. -/
abbrev FixedMSet (m K : ℕ) :=
  {s : Finset (Arm K) // s.card = m ∧ s.Nonempty}

/-- The finite support of all fixed `m`-sets of arms. -/
noncomputable def fixedMSetSupport (m K : ℕ) : Finset (FixedMSet m K) := by
  classical
  exact Finset.univ

/-- The support of fixed `m`-sets is finite and nonempty whenever `0 < m ≤ K`. -/
theorem fixedMSetSupport_nonempty {m K : ℕ} (hm : 0 < m) (hmK : m ≤ K) :
    (fixedMSetSupport m K).Nonempty := by
  classical
  let arms : Finset (Arm K) :=
    (Finset.univ : Finset (Fin m)).map (Fin.castLEEmb hmK)
  have hcard : arms.card = m := by
    dsimp [arms]
    rw [Finset.card_map, Finset.card_univ, Fintype.card_fin]
  have harms : arms.Nonempty := Finset.card_pos.mp (by rw [hcard]; exact hm)
  exact ⟨⟨arms, hcard, harms⟩, Finset.mem_univ _⟩

/-- Reward accumulated by a fixed set of arms over all rounds. -/
def fixedMSetReward {K T : ℕ} (rewards : RewardMatrix T K) (arms : Finset (Arm K)) : ℝ :=
  ∑ t : Fin T, ∑ a ∈ arms, rewards.reward t a

/-- Every fixed `m`-set earns a pathwise total in `[0,mT]`. -/
theorem fixedMSetReward_mem_Icc {m K T : ℕ} (rewards : RewardMatrix T K)
    (arms : FixedMSet m K) :
    fixedMSetReward rewards arms.val ∈ Set.Icc (0 : ℝ) ((m : ℝ) * (T : ℝ)) := by
  constructor
  · unfold fixedMSetReward
    apply Finset.sum_nonneg
    intro t ht
    apply Finset.sum_nonneg
    intro a ha
    exact (rewards.reward_mem_Icc t a).1
  · unfold fixedMSetReward
    calc
      (∑ t : Fin T, ∑ a ∈ arms.val, rewards.reward t a) ≤
          ∑ t : Fin T, ∑ a ∈ arms.val, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro t ht
        apply Finset.sum_le_sum
        intro a ha
        exact (rewards.reward_mem_Icc t a).2
      _ = (T : ℝ) * (m : ℝ) := by simp [arms.property.1]
      _ = (m : ℝ) * (T : ℝ) := by ring

/-- The literal best fixed `m`-set comparator, as a maximum over its finite nonempty support. -/
noncomputable def bestFixedMSetComparator {m K T : ℕ} (hm : 0 < m) (hmK : m ≤ K)
    (rewards : RewardMatrix T K) : ℝ :=
  (fixedMSetSupport m K).sup' (fixedMSetSupport_nonempty hm hmK)
    (fun arms => fixedMSetReward rewards arms.val)

/-- The finite best fixed-set comparator is also in `[0,mT]`. -/
theorem bestFixedMSetComparator_mem_Icc {m K T : ℕ} (hm : 0 < m) (hmK : m ≤ K)
    (rewards : RewardMatrix T K) :
    bestFixedMSetComparator hm hmK rewards ∈ Set.Icc (0 : ℝ) ((m : ℝ) * (T : ℝ)) := by
  constructor
  · unfold bestFixedMSetComparator
    obtain ⟨arms, harms⟩ := fixedMSetSupport_nonempty hm hmK
    apply (Finset.le_sup'_iff (fixedMSetSupport_nonempty hm hmK)).mpr
    exact ⟨arms, harms, (fixedMSetReward_mem_Icc rewards arms).1⟩
  · unfold bestFixedMSetComparator
    apply Finset.sup'_le
    intro arms harms
    exact (fixedMSetReward_mem_Icc rewards arms).2

end Bandits.Support.FiniteBanditModel

end
