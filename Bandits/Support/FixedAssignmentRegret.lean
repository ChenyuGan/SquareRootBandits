module

public import Bandits.Support.FiniteBanditModel
import Mathlib.Tactic.Ring

/-!
# Deterministic fixed assignment

The fixed-assignment branch is described in
`sources/zip4/manuscript/07_public_setup.tex:5-9` and its regret comparison in
`sources/zip4/manuscript/08_main_theorem.tex:170-175`. The environment,
collision feedback, and fixed-set comparator are those of
`sources/zip4/manuscript/01_introduction.tex:19-36`.

This module proves the deterministic fallback bound for every bounded real
reward matrix and every finite horizon. It does not prove the construction
branch or the main theorem.
-/

public section

namespace Bandits.Support.FixedAssignmentRegret

open Bandits.Support.FiniteBanditModel

/-- The arms assigned to players by the source's fixed-assignment branch. -/
@[expose] def fixedAssignmentArms {m K : ℕ} (hmK : m ≤ K) : Finset (Arm K) :=
  (Finset.univ : Finset (Player m)).map (Fin.castLEEmb hmK)

/-- Each player always chooses its one-based source arm, ignoring every input and history. -/
@[expose] def fixedAssignmentPolicy {m K : ℕ} (hmK : m ≤ K)
    {PublicData PrivateInput : Type*} : PlayerLocalDecision m K PublicData PrivateInput :=
  fun i _ _ _ _ => Fin.castLE hmK i

/-- The recursively constructed prefix uses the assigned arm at every round. -/
theorem deterministicRolloutPrefix_action_eq_fixedAssignment {m K T : ℕ}
    {PublicData PrivateInput : Type*} (hmK : m ≤ K)
    (publicData : PublicData) (privateInput : Player m → PrivateInput)
    (rewards : RewardMatrix T K) :
    ∀ (t : ℕ) (ht : t ≤ T) (s : Fin t) (i : Player m),
      (deterministicRolloutPrefix (fixedAssignmentPolicy hmK) publicData privateInput rewards
        t ht).action s i = Fin.castLE hmK i := by
  intro t
  induction t with
  | zero =>
      intro ht s i
      exact Fin.elim0 s
  | succ t ih =>
      intro ht s i
      cases s using Fin.lastCases with
      | last =>
          rw [deterministicRolloutPrefix_action_last]
          rfl
      | cast s =>
          rw [deterministicRolloutPrefix_action_castSucc]
          exact ih (Nat.le_of_succ_le ht) s i

/-- The recursive rollout stores exactly the collision feedback of each stored action. -/
theorem deterministicRolloutPrefix_feedback_eq_playerFeedback {m K T : ℕ}
    {PublicData PrivateInput : Type*}
    (decide : PlayerLocalDecision m K PublicData PrivateInput) (publicData : PublicData)
    (privateInput : Player m → PrivateInput) (rewards : RewardMatrix T K) :
    ∀ (t : ℕ) (ht : t ≤ T) (s : Fin t) (i : Player m),
      (deterministicRolloutPrefix decide publicData privateInput rewards t ht).feedback s i =
        playerFeedback
          ((deterministicRolloutPrefix decide publicData privateInput rewards t ht).action s)
          (rewards.reward (Fin.castLE ht s)) i := by
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
          have hprofile :
              (deterministicRolloutPrefix decide publicData privateInput rewards (t + 1) ht).action
                  (Fin.last t) =
                fun j => decide j t publicData
                  (localHistoryOfRun
                    (deterministicRolloutPrefix decide publicData privateInput rewards t
                      (Nat.le_of_succ_le ht)) j)
                  (privateInput j) := by
            funext j
            exact deterministicRolloutPrefix_action_last decide publicData privateInput rewards
              t ht j
          rw [hprofile]
      | cast s =>
          rw [deterministicRolloutPrefix_feedback_castSucc]
          rw [ih (Nat.le_of_succ_le ht) s i]
          have hprofile :
              (deterministicRolloutPrefix decide publicData privateInput rewards (t + 1) ht).action
                  s.castSucc =
                (deterministicRolloutPrefix decide publicData privateInput rewards t
                  (Nat.le_of_succ_le ht)).action s := by
            funext j
            exact deterministicRolloutPrefix_action_castSucc decide publicData privateInput rewards
              t ht s j
          rw [hprofile]
          have hrow : Fin.castLE ht s.castSucc =
              Fin.castLE (Nat.le_of_succ_le ht) s := by
            apply Fin.ext
            rfl
          rw [hrow]

/-- The complete rollout feedback is the collision feedback of its stored action. -/
theorem deterministicRollout_feedback_eq_playerFeedback {m K T : ℕ}
    {PublicData PrivateInput : Type*}
    (decide : PlayerLocalDecision m K PublicData PrivateInput) (publicData : PublicData)
    (privateInput : Player m → PrivateInput) (rewards : RewardMatrix T K)
    (t : Fin T) (i : Player m) :
    (deterministicRollout decide publicData privateInput rewards).feedback t i =
      playerFeedback ((deterministicRollout decide publicData privateInput rewards).action t)
        (rewards.reward t) i := by
  simpa only [deterministicRollout, Fin.castLE_rfl, id_eq] using
    deterministicRolloutPrefix_feedback_eq_playerFeedback decide publicData privateInput rewards
      T (Nat.le_refl T) t i

/-- The complete deterministic rollout plays the fixed injective assignment. -/
theorem deterministicRollout_action_eq_fixedAssignment {m K T : ℕ}
    {PublicData PrivateInput : Type*} (hmK : m ≤ K)
    (publicData : PublicData) (privateInput : Player m → PrivateInput)
    (rewards : RewardMatrix T K) (t : Fin T) (i : Player m) :
    (deterministicRollout (fixedAssignmentPolicy hmK) publicData privateInput rewards).action
      t i = Fin.castLE hmK i := by
  exact deterministicRolloutPrefix_action_eq_fixedAssignment hmK publicData privateInput
    rewards T (Nat.le_refl T) t i

/-- The fallback rollout's action profile is injective, as derived from its actions. -/
theorem deterministicRollout_action_injective {m K T : ℕ}
    {PublicData PrivateInput : Type*} (hmK : m ≤ K)
    (publicData : PublicData) (privateInput : Player m → PrivateInput)
    (rewards : RewardMatrix T K) (t : Fin T) :
    Function.Injective
      ((deterministicRollout (fixedAssignmentPolicy hmK) publicData privateInput rewards).action t) := by
  intro i j hij
  apply Fin.castLE_injective hmK
  rw [← deterministicRollout_action_eq_fixedAssignment hmK publicData privateInput rewards t i,
    ← deterministicRollout_action_eq_fixedAssignment hmK publicData privateInput rewards t j]
  exact hij

/-- The rollout action image is exactly the image fixed `m`-set. -/
theorem deterministicRollout_action_image_eq_fixedAssignment {m K T : ℕ}
    {PublicData PrivateInput : Type*} (hmK : m ≤ K)
    (publicData : PublicData) (privateInput : Player m → PrivateInput)
    (rewards : RewardMatrix T K) (t : Fin T) :
    (Finset.univ : Finset (Player m)).image
        ((deterministicRollout (fixedAssignmentPolicy hmK) publicData privateInput rewards).action t) =
      fixedAssignmentArms hmK := by
  classical
  ext a
  constructor
  · intro ha
    rcases Finset.mem_image.mp ha with ⟨i, hi, hia⟩
    apply Finset.mem_map.mpr
    refine ⟨i, Finset.mem_univ i, ?_⟩
    have hia' := hia
    rw [deterministicRollout_action_eq_fixedAssignment hmK publicData privateInput rewards t i]
      at hia'
    simpa only [Fin.coe_castLEEmb] using hia'
  · intro ha
    rcases Finset.mem_map.mp ha with ⟨i, hi, hia⟩
    apply Finset.mem_image.mpr
    refine ⟨i, Finset.mem_univ i, ?_⟩
    rw [deterministicRollout_action_eq_fixedAssignment hmK publicData privateInput rewards t i]
    simpa only [Fin.coe_castLEEmb] using hia

/-- The assignment has exactly `m` arms. -/
theorem fixedAssignmentArms_card {m K : ℕ} (hmK : m ≤ K) :
    (fixedAssignmentArms hmK).card = m := by
  rw [fixedAssignmentArms, Finset.card_map, Finset.card_univ, Fintype.card_fin]

/-- Cumulative physical feedback is the reward of the assigned image set. -/
theorem deterministicRollout_pathwiseCumulativeReward_eq_fixedAssignment {m K T : ℕ}
    {PublicData PrivateInput : Type*} (hmK : m ≤ K)
    (publicData : PublicData) (privateInput : Player m → PrivateInput)
    (rewards : RewardMatrix T K) :
    pathwiseCumulativeReward
        (deterministicRollout (fixedAssignmentPolicy hmK) publicData privateInput rewards) =
      fixedMSetReward rewards (fixedAssignmentArms hmK) := by
  classical
  unfold pathwiseCumulativeReward fixedMSetReward
  apply Finset.sum_congr rfl
  intro t ht
  calc
    (∑ i : Player m,
        (deterministicRollout (fixedAssignmentPolicy hmK) publicData privateInput rewards).feedback
          t i) =
        ∑ i : Player m, playerFeedback
          ((deterministicRollout (fixedAssignmentPolicy hmK) publicData privateInput rewards).action t)
          (rewards.reward t) i := by
      apply Finset.sum_congr rfl
      intro i hi
      exact deterministicRollout_feedback_eq_playerFeedback (fixedAssignmentPolicy hmK) publicData
        privateInput rewards t i
    _ = ∑ a ∈ (Finset.univ : Finset (Player m)).image
          ((deterministicRollout (fixedAssignmentPolicy hmK) publicData privateInput rewards).action
            t), rewards.reward t a :=
      feedback_sum_eq_image_reward_of_injective _ _
        (deterministicRollout_action_injective hmK publicData privateInput rewards t)
    _ = ∑ a ∈ fixedAssignmentArms hmK, rewards.reward t a := by
      rw [deterministicRollout_action_image_eq_fixedAssignment hmK publicData privateInput rewards t]

/-- Compare two equal-size arm sets by the rewards in their actual set differences. -/
theorem fixedMSetReward_sub_le_of_card_eq {m K T : ℕ}
    (rewards : RewardMatrix T K) (S S' : Finset (Arm K))
    (hS : S.card = m) (hS' : S'.card = m) :
    fixedMSetReward rewards S - fixedMSetReward rewards S' ≤
      (min m (K - m) : ℝ) * (T : ℝ) := by
  classical
  have hmK : m ≤ K := by
    calc
      m = S.card := hS.symm
      _ ≤ (Finset.univ : Finset (Arm K)).card :=
        Finset.card_le_card (Finset.subset_univ S)
      _ = K := by simp
  have hdiff_card_m : (S \ S').card ≤ m := by
    calc
      (S \ S').card ≤ S.card := Finset.card_le_card Finset.sdiff_subset
      _ = m := hS
  have hdiff_subset_compl : S' \ S ⊆ (Finset.univ : Finset (Arm K)) \ S := by
    intro a ha
    simp only [Finset.mem_sdiff] at ha ⊢
    exact ⟨Finset.mem_univ a, ha.2⟩
  have hcompl_card : ((Finset.univ : Finset (Arm K)) \ S).card = K - m := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ S)]
    simp [hS]
  have hdiff_card_compl : (S \ S').card ≤ K - m := by
    calc
      (S \ S').card = (S' \ S).card :=
        Finset.card_sdiff_comm (hS.trans hS'.symm)
      _ ≤ ((Finset.univ : Finset (Arm K)) \ S).card :=
        Finset.card_le_card hdiff_subset_compl
      _ = K - m := hcompl_card
  have hdiff_card : (S \ S').card ≤ min m (K - m) :=
    Nat.le_min.mpr ⟨hdiff_card_m, hdiff_card_compl⟩
  have hround (t : Fin T) :
      (∑ a ∈ S, rewards.reward t a) - (∑ a ∈ S', rewards.reward t a) ≤
        (min m (K - m) : ℝ) := by
    rw [← Finset.sum_sdiff_sub_sum_sdiff]
    have hupper :
        (∑ a ∈ S \ S', rewards.reward t a) ≤ ((S \ S').card : ℝ) := by
      calc
        (∑ a ∈ S \ S', rewards.reward t a) ≤ ∑ _a ∈ S \ S', (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro a ha
          exact (rewards.reward_mem_Icc t a).2
        _ = ((S \ S').card : ℝ) := by simp
    have hlower : 0 ≤ ∑ a ∈ S' \ S, rewards.reward t a := by
      apply Finset.sum_nonneg
      intro a ha
      exact (rewards.reward_mem_Icc t a).1
    calc
      (∑ a ∈ S \ S', rewards.reward t a) - (∑ a ∈ S' \ S, rewards.reward t a) ≤
          ((S \ S').card : ℝ) - 0 := sub_le_sub hupper hlower
      _ = ((S \ S').card : ℝ) := by ring
      _ ≤ (min m (K - m) : ℝ) := by exact_mod_cast hdiff_card
  unfold fixedMSetReward
  rw [← Finset.sum_sub_distrib]
  calc
    (∑ t : Fin T, ((∑ a ∈ S, rewards.reward t a) - (∑ a ∈ S', rewards.reward t a))) ≤
        ∑ _t : Fin T, (min m (K - m) : ℝ) :=
      Finset.sum_le_sum fun t ht => hround t
    _ = (min m (K - m) : ℝ) * (T : ℝ) := by simp [mul_comm]

/-- Every fixed `m`-set has regret at most the sharp finite-set difference bound. -/
theorem fixedAssignment_anyFixedMSet_regret_le {m K T : ℕ} (hmK : m ≤ K)
    (rewards : RewardMatrix T K) (S : FixedMSet m K)
    {PublicData PrivateInput : Type*} (publicData : PublicData)
    (privateInput : Player m → PrivateInput) :
    fixedMSetReward rewards S.val -
        pathwiseCumulativeReward
          (deterministicRollout (fixedAssignmentPolicy hmK) publicData privateInput rewards) ≤
      (min m (K - m) : ℝ) * (T : ℝ) := by
  rw [deterministicRollout_pathwiseCumulativeReward_eq_fixedAssignment hmK publicData
    privateInput rewards]
  exact fixedMSetReward_sub_le_of_card_eq rewards S.val (fixedAssignmentArms hmK)
    S.property.1 (fixedAssignmentArms_card hmK)

/-- The literal best fixed-set comparator obeys the same deterministic regret bound. -/
theorem bestFixedMSetComparator_regret_le {m K T : ℕ} (hm : 0 < m) (hmK : m ≤ K)
    (rewards : RewardMatrix T K) {PublicData PrivateInput : Type*}
    (publicData : PublicData) (privateInput : Player m → PrivateInput) :
    bestFixedMSetComparator hm hmK rewards -
        pathwiseCumulativeReward
          (deterministicRollout (fixedAssignmentPolicy hmK) publicData privateInput rewards) ≤
      (min m (K - m) : ℝ) * (T : ℝ) := by
  rw [sub_le_iff_le_add, bestFixedMSetComparator]
  apply Finset.sup'_le
  intro S hS
  have h := fixedAssignment_anyFixedMSet_regret_le hmK rewards S publicData privateInput
  exact (sub_le_iff_le_add.mp h)

/-- The fallback regret is also at most `m*T`. -/
theorem bestFixedMSetComparator_regret_le_m_mul_T {m K T : ℕ} (hm : 0 < m) (hmK : m ≤ K)
    (rewards : RewardMatrix T K) {PublicData PrivateInput : Type*}
    (publicData : PublicData) (privateInput : Player m → PrivateInput) :
    bestFixedMSetComparator hm hmK rewards -
        pathwiseCumulativeReward
          (deterministicRollout (fixedAssignmentPolicy hmK) publicData privateInput rewards) ≤
      (m : ℝ) * (T : ℝ) := by
  have hmin : (min m (K - m) : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast Nat.min_le_left m (K - m)
  exact (bestFixedMSetComparator_regret_le hm hmK rewards publicData privateInput).trans
    (mul_le_mul_of_nonneg_right hmin (Nat.cast_nonneg T))

/-- When all arms are assigned, the best-comparator regret is at most zero. -/
theorem bestFixedMSetComparator_regret_nonpos_of_eq {m K T : ℕ} (hm : 0 < m)
    (hmK : m ≤ K) (hmEq : m = K) (rewards : RewardMatrix T K)
    {PublicData PrivateInput : Type*} (publicData : PublicData)
    (privateInput : Player m → PrivateInput) :
    bestFixedMSetComparator hm hmK rewards -
        pathwiseCumulativeReward
          (deterministicRollout (fixedAssignmentPolicy hmK) publicData privateInput rewards) ≤ 0 := by
  simpa [hmEq] using
    bestFixedMSetComparator_regret_le hm hmK rewards publicData privateInput

end Bandits.Support.FixedAssignmentRegret

end
