/-
Copyright (c) 2026 Bandits contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.FiniteBanditModel
public import Bandits.Support.RealRewardGridCount
public import Bandits.Support.RewardRounding

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Local-policy comparison for rounded reward matrices

This module formalizes the deterministic comparison motivated by
`sources/zip4/manuscript/01_introduction.tex:19-36`,
`sources/zip4/manuscript/03_algorithm_overview.tex:3-7`,
`sources/zip4/manuscript/07_public_setup.tex:90-94`, and
`sources/zip4/manuscript/08_main_theorem.tex:163-168`. It applies to every
local decision rule, fixed public datum, and fixed profile of private inputs.
It compares actual prefixes built by `deterministicRolloutPrefix`; it does
not assert that the manuscript protocol is implemented.
-/

@[expose] public section

namespace Bandits.Support.RoundedLocalRollout

open Bandits.Support.FiniteBanditModel
open Bandits.Support.RealRewardGridCount
open Bandits.Support.RewardRounding

/-- The reward matrix obtained by rounding each entry of a bounded matrix down. -/
noncomputable def roundedRewardMatrix {T K : ℕ} (D : ℕ) (hD : 0 < D)
    (rewards : RewardMatrix T K) : RewardMatrix T K where
  reward t a := rounded D (rewards.reward t a)
  reward_mem_Icc t a := rounded_mem_unitInterval D (rewards.reward t a) hD
    (rewards.reward_mem_Icc t a)

/-- The floor index used to encode one bounded rounded real in `Fin (D + 1)`. -/
noncomputable def roundedIndex (D : ℕ) (_hD : 0 < D) (r : ℝ)
    (hr : r ∈ Set.Icc (0 : ℝ) 1) : Fin (D + 1) := by
  have hDreal : (0 : ℝ) ≤ (D : ℝ) := Nat.cast_nonneg D
  have hfloor :
      (Nat.floor ((D : ℝ) * r) : ℝ) ≤ (D : ℝ) := by
    calc
      (Nat.floor ((D : ℝ) * r) : ℝ) ≤ (D : ℝ) * r :=
        Nat.floor_le (mul_nonneg hDreal hr.1)
      _ ≤ (D : ℝ) := by
        exact mul_le_of_le_one_right hDreal hr.2
  have hfloorNat : Nat.floor ((D : ℝ) * r) ≤ D := by
    exact_mod_cast hfloor
  exact ⟨Nat.floor ((D : ℝ) * r), Nat.lt_succ_of_le hfloorNat⟩

/-- The floor index used to encode one rounded matrix entry. -/
noncomputable def roundedRewardIndex {T K : ℕ} (D : ℕ) (hD : 0 < D)
    (rewards : RewardMatrix T K) (t : Fin T) (a : Arm K) : Fin (D + 1) :=
  roundedIndex D hD (rewards.reward t a) (rewards.reward_mem_Icc t a)

/-- The pointwise finite-index encoding of the rounded reward matrix. -/
noncomputable def roundedRewardMatrixCode {T K : ℕ} (D : ℕ) (hD : 0 < D)
    (rewards : RewardMatrix T K) : Fin T → Fin K → Fin (D + 1) :=
  fun t a => roundedRewardIndex D hD rewards t a

/-- A rounded entry is exactly the real grid value selected by its floor index. -/
theorem roundedRewardMatrixCode_value {T K : ℕ} (D : ℕ) (hD : 0 < D)
    (rewards : RewardMatrix T K) (t : Fin T) (a : Arm K) :
    realRewardGridValue D hD (roundedRewardIndex D hD rewards t a) =
      rounded D (rewards.reward t a) := by
  rfl

/-- Every rounded bounded scalar is a member of the existing real reward grid. -/
theorem rounded_mem_grid {D : ℕ} (hD : 0 < D) {r : ℝ}
    (hr : r ∈ Set.Icc (0 : ℝ) 1) : rounded D r ∈ realRewardGrid D hD := by
  rw [realRewardGrid]
  exact ⟨roundedIndex D hD r hr, by rfl⟩

/-- Every rounded matrix entry belongs to the already-defined real reward grid. -/
theorem roundedRewardMatrix_mem_grid {T K : ℕ} (D : ℕ) (hD : 0 < D)
    (rewards : RewardMatrix T K) (t : Fin T) (a : Arm K) :
    rounded D (rewards.reward t a) ∈ realRewardGrid D hD := by
  exact rounded_mem_grid hD (rewards.reward_mem_Icc t a)

/-- The existing finite-to-real grid equivalence sends the rounded code to the
corresponding rounded matrix entry. -/
theorem roundedRewardMatrixCode_equiv_value {T K : ℕ} (D : ℕ) (hD : 0 < D)
    (rewards : RewardMatrix T K) (t : Fin T) (a : Arm K) :
    ((realRewardMatrixEncodingEquiv D K T hD (roundedRewardMatrixCode D hD rewards))
      t a).val = (roundedRewardMatrix D hD rewards).reward t a := by
  rfl

/-- Rounding preserves zero, including the degenerate denominator case. -/
@[simp] theorem rounded_zero (D : ℕ) : rounded D 0 = 0 := by
  simp [rounded]

/-- Every bounded real-grid value is fixed by rounding at that denominator. -/
theorem rounded_eq_of_mem_grid (D : ℕ) (hD : 0 < D) {r : ℝ}
    (hr : r ∈ realRewardGrid D hD) : rounded D r = r := by
  rcases hr with ⟨k, rfl⟩
  have hDreal : (D : ℝ) ≠ 0 := (Nat.cast_pos.mpr hD).ne'
  unfold rounded realRewardGridValue
  have hmul : (D : ℝ) * ((k : ℝ) / (D : ℝ)) = (k : ℝ) := by
    field_simp
  rw [hmul, Nat.floor_natCast]

/-- Rounding is idempotent on the unit interval. -/
theorem rounded_idempotent (D : ℕ) (hD : 0 < D) {r : ℝ}
    (hr : r ∈ Set.Icc (0 : ℝ) 1) : rounded D (rounded D r) = rounded D r := by
  apply rounded_eq_of_mem_grid D hD
  exact rounded_mem_grid hD hr

/-- Rounding commutes with collision feedback, because a collision returns zero. -/
theorem rounded_playerFeedback {m K : ℕ} (D : ℕ) (actions : ActionProfile m K)
    (rewards : Arm K → ℝ) (i : Player m) :
    rounded D (playerFeedback actions rewards i) =
      playerFeedback actions (fun a => rounded D (rewards a)) i := by
  classical
  by_cases hfree : collisionFreeFor actions i
  · simp [playerFeedback, hfree]
  · simp [playerFeedback, hfree]

/-- Collision feedback on a row whose rewards lie in the real grid also lies
in that grid, since a collision contributes the grid value zero. -/
theorem playerFeedback_mem_grid {m K : ℕ} (D : ℕ) (hD : 0 < D)
    (actions : ActionProfile m K) (rewards : Arm K → ℝ)
    (hrewards : ∀ a, rewards a ∈ realRewardGrid D hD) (i : Player m) :
    playerFeedback actions rewards i ∈ realRewardGrid D hD := by
  classical
  by_cases hfree : collisionFreeFor actions i
  · simpa [playerFeedback, hfree] using hrewards (actions i)
  · have hzero : (0 : ℝ) ∈ realRewardGrid D hD := by
      simpa using (rounded_mem_grid (D := D) hD (r := (0 : ℝ)) (by norm_num))
    simpa [playerFeedback, hfree] using hzero

/-- Apply scalar rounding to every observation in a local history, preserving
the player's past actions. -/
noncomputable def roundLocalHistory {K t : ℕ} (D : ℕ)
    (history : LocalHistory K t) : LocalHistory K t :=
  fun s => ((history s).1, rounded D (history s).2)

/-- A local policy wrapper that rounds only the observations in its own history. -/
noncomputable def roundedLocalDecision {m K : ℕ} {PublicData PrivateInput : Type*} (D : ℕ)
    (decide : PlayerLocalDecision m K PublicData PrivateInput) :
    PlayerLocalDecision m K PublicData PrivateInput :=
  fun i t publicData history privateInput =>
    decide i t publicData (roundLocalHistory D history) privateInput

/-- The actual prefixes under the wrapper and the original and rounded reward
matrices choose the same actions, and rounding the original feedback gives the
feedback in the rounded-matrix run. -/
theorem roundedLocalRolloutPrefix_invariant {m K T : ℕ}
    {PublicData PrivateInput : Type*} (D : ℕ) (hD : 0 < D)
    (decide : PlayerLocalDecision m K PublicData PrivateInput)
    (publicData : PublicData) (privateInput : Player m → PrivateInput)
    (rewards : RewardMatrix T K) :
    ∀ (t : ℕ) (ht : t ≤ T),
      (∀ s : Fin t, ∀ i : Player m,
        (deterministicRolloutPrefix (roundedLocalDecision D decide) publicData privateInput
          rewards t ht).action s i =
        (deterministicRolloutPrefix (roundedLocalDecision D decide) publicData privateInput
          (roundedRewardMatrix D hD rewards) t ht).action s i) ∧
      (∀ s : Fin t, ∀ i : Player m,
        rounded D ((deterministicRolloutPrefix (roundedLocalDecision D decide) publicData
          privateInput rewards t ht).feedback s i) =
        (deterministicRolloutPrefix (roundedLocalDecision D decide) publicData privateInput
          (roundedRewardMatrix D hD rewards) t ht).feedback s i) := by
  intro t
  induction t with
  | zero =>
      intro ht
      constructor
      · intro s
        exact Fin.elim0 s
      · intro s
        exact Fin.elim0 s
  | succ t ih =>
      intro ht
      have hprev := ih (Nat.le_of_succ_le ht)
      let originalPrev := deterministicRolloutPrefix (roundedLocalDecision D decide)
        publicData privateInput rewards t (Nat.le_of_succ_le ht)
      let roundedPrev := deterministicRolloutPrefix (roundedLocalDecision D decide)
        publicData privateInput (roundedRewardMatrix D hD rewards) t
          (Nat.le_of_succ_le ht)
      have hhistory (i : Player m) :
          roundLocalHistory D (localHistoryOfRun originalPrev i) =
            roundLocalHistory D (localHistoryOfRun roundedPrev i) := by
        funext s
        apply Prod.ext
        · change originalPrev.action s i = roundedPrev.action s i
          exact hprev.1 s i
        · change rounded D (originalPrev.feedback s i) =
            rounded D (roundedPrev.feedback s i)
          rw [hprev.2 s i]
          apply (rounded_eq_of_mem_grid D hD ?_).symm
          rw [← hprev.2 s i]
          exact rounded_mem_grid hD
            (deterministicRolloutPrefix_feedback_mem_Icc
              (roundedLocalDecision D decide) publicData privateInput rewards t
              (Nat.le_of_succ_le ht) s i)
      constructor
      · intro s i
        cases s using Fin.lastCases with
        | cast s =>
            rw [deterministicRolloutPrefix_action_castSucc,
              deterministicRolloutPrefix_action_castSucc]
            exact hprev.1 s i
        | last =>
            rw [deterministicRolloutPrefix_action_last,
              deterministicRolloutPrefix_action_last]
            change decide i t publicData
                (roundLocalHistory D (localHistoryOfRun originalPrev i)) (privateInput i) =
              decide i t publicData
                (roundLocalHistory D (localHistoryOfRun roundedPrev i)) (privateInput i)
            rw [hhistory i]
      · intro s i
        cases s using Fin.lastCases with
        | cast s =>
            rw [deterministicRolloutPrefix_feedback_castSucc,
              deterministicRolloutPrefix_feedback_castSucc]
            exact hprev.2 s i
        | last =>
            rw [deterministicRolloutPrefix_feedback_last,
              deterministicRolloutPrefix_feedback_last]
            have hprofile :
                (fun j : Player m =>
                  decide j t publicData
                    (roundLocalHistory D (localHistoryOfRun originalPrev j)) (privateInput j)) =
                (fun j : Player m =>
                  decide j t publicData
                    (roundLocalHistory D (localHistoryOfRun roundedPrev j)) (privateInput j)) := by
              funext j
              rw [hhistory j]
            simp only [roundedLocalDecision, roundedRewardMatrix]
            rw [hprofile]
            exact rounded_playerFeedback D
              (fun j => decide j t publicData
                (roundLocalHistory D (localHistoryOfRun roundedPrev j)) (privateInput j))
              (rewards.reward (Fin.castLE ht (Fin.last t))) i

/-- Under the rounded matrix, the local wrapper acts exactly like its base
policy on the already rounded local histories. -/
theorem roundedLocalDecision_on_grid_histories {m K : ℕ}
    {PublicData PrivateInput : Type*} (D : ℕ) (hD : 0 < D)
    (decide : PlayerLocalDecision m K PublicData PrivateInput)
    (i : Player m) (t : ℕ) (publicData : PublicData)
    (history : LocalHistory K t) (privateInput : PrivateInput)
    (hgrid : ∀ s, (history s).2 ∈ realRewardGrid D hD) :
    roundedLocalDecision D decide i t publicData history privateInput =
      decide i t publicData history privateInput := by
  simp only [roundedLocalDecision]
  have hhistory : roundLocalHistory D history = history := by
    funext s
    apply Prod.ext
    · rfl
    · exact rounded_eq_of_mem_grid D hD (hgrid s)
  exact congrArg (decide i t publicData · privateInput) hhistory

/-- Physical cumulative reward in the original run is at least that in the
rounded-matrix run. -/
theorem roundedLocalRollout_physicalReward_ge {m K T : ℕ}
    {PublicData PrivateInput : Type*} (D : ℕ) (hD : 0 < D)
    (decide : PlayerLocalDecision m K PublicData PrivateInput)
    (publicData : PublicData) (privateInput : Player m → PrivateInput)
    (rewards : RewardMatrix T K) :
    pathwiseCumulativeReward
        (deterministicRollout (roundedLocalDecision D decide) publicData privateInput rewards) ≥
      pathwiseCumulativeReward
        (deterministicRollout (roundedLocalDecision D decide) publicData privateInput
          (roundedRewardMatrix D hD rewards)) := by
  have hprefix := roundedLocalRolloutPrefix_invariant D hD decide publicData privateInput rewards
    T (Nat.le_refl T)
  unfold pathwiseCumulativeReward
  apply Finset.sum_le_sum
  intro t ht
  apply Finset.sum_le_sum
  intro i hi
  have hround := hprefix.2 t i
  change rounded D ((deterministicRollout (roundedLocalDecision D decide) publicData
    privateInput rewards).feedback t i) =
      (deterministicRollout (roundedLocalDecision D decide) publicData privateInput
        (roundedRewardMatrix D hD rewards)).feedback t i at hround
  have hbound := deterministicRollout_feedback_mem_Icc
    (roundedLocalDecision D decide) publicData privateInput rewards t i
  rw [← hround]
  exact rounded_le D _ hD hbound.1

/-- For each fixed `m`-set, entrywise rounding loses at most `m*T/D`. -/
theorem fixedMSetReward_rounding_le {m K T : ℕ} (D : ℕ) (hD : 0 < D)
    (rewards : RewardMatrix T K) (arms : FixedMSet m K) :
    fixedMSetReward rewards arms.val ≤
      fixedMSetReward (roundedRewardMatrix D hD rewards) arms.val +
        (m : ℝ) * (T : ℝ) / (D : ℝ) := by
  have hround (t : Fin T) :
      (∑ a ∈ arms.val, rewards.reward t a) -
          (∑ a ∈ arms.val, rounded D (rewards.reward t a)) ≤
        (arms.val.card : ℝ) / (D : ℝ) := by
    have hsum := sum_error_le_card_div arms.val D
      (fun a => rewards.reward t a) (fun a => rounded D (rewards.reward t a))
      (fun a ha => sub_rounded_lt_inv D (rewards.reward t a) hD)
    have hrewrite :
        (∑ a ∈ arms.val, (rewards.reward t a - rounded D (rewards.reward t a))) =
          (∑ a ∈ arms.val, rewards.reward t a) -
            (∑ a ∈ arms.val, rounded D (rewards.reward t a)) := by
      rw [Finset.sum_sub_distrib]
    rw [← hrewrite]
    exact hsum
  have htime :
      (∑ t : Fin T, ∑ a ∈ arms.val, rewards.reward t a) -
          (∑ t : Fin T, ∑ a ∈ arms.val, rounded D (rewards.reward t a)) ≤
        (T : ℝ) * ((arms.val.card : ℝ) / (D : ℝ)) := by
    rw [← Finset.sum_sub_distrib]
    calc
      (∑ t : Fin T,
          ((∑ a ∈ arms.val, rewards.reward t a) -
            (∑ a ∈ arms.val, rounded D (rewards.reward t a)))) ≤
          ∑ t : Fin T, ((arms.val.card : ℝ) / (D : ℝ)) :=
        Finset.sum_le_sum (fun t ht => hround t)
      _ = (T : ℝ) * ((arms.val.card : ℝ) / (D : ℝ)) := by simp
  have hcard : (arms.val.card : ℝ) = (m : ℝ) := by
    exact_mod_cast arms.property.1
  change (∑ t : Fin T, ∑ a ∈ arms.val, rewards.reward t a) ≤
      (∑ t : Fin T, ∑ a ∈ arms.val, rounded D (rewards.reward t a)) +
        (m : ℝ) * (T : ℝ) / (D : ℝ)
  have hdiff :
      (∑ t : Fin T, ∑ a ∈ arms.val, rewards.reward t a) -
        (∑ t : Fin T, ∑ a ∈ arms.val, rounded D (rewards.reward t a)) ≤
          (m : ℝ) * (T : ℝ) / (D : ℝ) := by
    calc
      (∑ t : Fin T, ∑ a ∈ arms.val, rewards.reward t a) -
          (∑ t : Fin T, ∑ a ∈ arms.val, rounded D (rewards.reward t a)) ≤
        (T : ℝ) * ((arms.val.card : ℝ) / (D : ℝ)) := htime
      _ = (m : ℝ) * (T : ℝ) / (D : ℝ) := by rw [hcard]; ring
  linarith

/-- The best fixed-set comparator on the original matrix is at most the rounded
comparator plus `m*T/D`. -/
theorem bestFixedMSetComparator_rounding_le {m K T : ℕ} (hm : 0 < m) (hmK : m ≤ K)
    (D : ℕ) (hD : 0 < D) (rewards : RewardMatrix T K) :
    bestFixedMSetComparator hm hmK rewards ≤
      bestFixedMSetComparator hm hmK (roundedRewardMatrix D hD rewards) +
        (m : ℝ) * (T : ℝ) / (D : ℝ) := by
  unfold bestFixedMSetComparator
  apply Finset.sup'_le
  intro arms harms
  calc
    fixedMSetReward rewards arms.val ≤
        fixedMSetReward (roundedRewardMatrix D hD rewards) arms.val +
          (m : ℝ) * (T : ℝ) / (D : ℝ) :=
      fixedMSetReward_rounding_le D hD rewards arms
    _ ≤ (fixedMSetSupport m K).sup'
          (fixedMSetSupport_nonempty hm hmK)
          (fun arms => fixedMSetReward (roundedRewardMatrix D hD rewards) arms.val) +
          (m : ℝ) * (T : ℝ) / (D : ℝ) := by
        apply add_le_add_left
        apply (Finset.le_sup'_iff (fixedMSetSupport_nonempty hm hmK)).mpr
        exact ⟨arms, harms, le_rfl⟩

/-- The deterministic regret difference is bounded by the rounded-run regret
plus the comparator rounding cost. This is pointwise in the public datum, the
original real reward matrix, and the fixed private-input profile. -/
theorem roundedLocalRollout_regret_le {m K T : ℕ}
    {PublicData PrivateInput : Type*} (hm : 0 < m) (hmK : m ≤ K)
    (D : ℕ) (hD : 0 < D) (decide : PlayerLocalDecision m K PublicData PrivateInput)
    (publicData : PublicData) (privateInput : Player m → PrivateInput)
    (rewards : RewardMatrix T K) :
    bestFixedMSetComparator hm hmK rewards -
        pathwiseCumulativeReward
          (deterministicRollout (roundedLocalDecision D decide) publicData privateInput rewards) ≤
      bestFixedMSetComparator hm hmK (roundedRewardMatrix D hD rewards) -
        pathwiseCumulativeReward
          (deterministicRollout (roundedLocalDecision D decide) publicData privateInput
            (roundedRewardMatrix D hD rewards)) +
        (m : ℝ) * (T : ℝ) / (D : ℝ) := by
  have hcomp := bestFixedMSetComparator_rounding_le hm hmK D hD rewards
  have hphys := roundedLocalRollout_physicalReward_ge D hD decide publicData privateInput rewards
  linarith

end Bandits.Support.RoundedLocalRollout

end
