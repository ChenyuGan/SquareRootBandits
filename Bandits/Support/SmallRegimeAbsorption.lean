module

public import Bandits.Support.ConstructorDimensions
public import Bandits.Support.FixedAssignmentRegret
public import Bandits.Support.PublicGridConcentration

import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Small-regime fixed-assignment absorption

The source uses a fixed assignment on the complement of its construction
branch (`sources/zip4/manuscript/07_public_setup.tex:5-9`). The regret scale
comparison is stated in `sources/zip4/manuscript/08_main_theorem.tex:170-175`.

This module proves the two complementary-branch scale estimates for the
literal `rowConcentrationScale` and applies the checked fixed-assignment regret
bound. It is an internal branch consumer, not a statement or closure of the
source-facing main theorem.
-/

public section

namespace Bandits.Support.SmallRegimeAbsorption

open Bandits.Support.ConstructorDimensions
open Bandits.Support.FixedAssignmentRegret
open Bandits.Support.FiniteBanditModel
open Bandits.Support.PublicGridConcentration

/-- The source small-horizon condition implies `m T ≤ sqrt(C_b) V`, where
`V` is the literal public-grid concentration scale. `C_b` precedes `p` so it
is uniform in all constructor dimensions. -/
theorem m_mul_T_le_sqrt_constant_mul_rowConcentrationScale_of_horizon
    (C_b : ℝ) (hC_b : 0 ≤ C_b) (p : ConstructorDimensions.Parameters)
    (hT : (p.T : ℝ) ≤ C_b * (p.m : ℝ) * (p.K : ℝ) *
      (b_N p : ℝ) ^ 2) :
    (p.m : ℝ) * (p.T : ℝ) ≤ Real.sqrt C_b * rowConcentrationScale p := by
  have hm_nonneg : 0 ≤ (p.m : ℝ) := Nat.cast_nonneg _
  have hT_nonneg : 0 ≤ (p.T : ℝ) := Nat.cast_nonneg _
  have hx_nonneg : 0 ≤ (p.m : ℝ) * (p.T : ℝ) :=
    mul_nonneg hm_nonneg hT_nonneg
  have hscale_nonneg := rowConcentrationScale_nonneg p
  have hy_nonneg : 0 ≤ Real.sqrt C_b * rowConcentrationScale p :=
    mul_nonneg (Real.sqrt_nonneg _) hscale_nonneg
  have hfactor_nonneg : 0 ≤ (p.m : ℝ) ^ 2 * (p.T : ℝ) :=
    mul_nonneg (sq_nonneg _) hT_nonneg
  have hmul := mul_le_mul_of_nonneg_right hT hfactor_nonneg
  have hsquare :
      ((p.m : ℝ) * (p.T : ℝ)) ^ 2 ≤ C_b * rowConcentrationScale p ^ 2 := by
    calc
      ((p.m : ℝ) * (p.T : ℝ)) ^ 2 =
          (p.T : ℝ) * ((p.m : ℝ) ^ 2 * (p.T : ℝ)) := by ring
      _ ≤
          (C_b * (p.m : ℝ) * (p.K : ℝ) * (b_N p : ℝ) ^ 2) *
            ((p.m : ℝ) ^ 2 * (p.T : ℝ)) := hmul
      _ = C_b * ((p.m : ℝ) ^ 3 * (p.K : ℝ) * (p.T : ℝ) *
            (b_N p : ℝ) ^ 2) := by ring
      _ = C_b * rowConcentrationScale p ^ 2 := by
        rw [rowConcentrationScale_sq]
  have hy_square :
      (Real.sqrt C_b * rowConcentrationScale p) ^ 2 =
        C_b * rowConcentrationScale p ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hC_b]
  rw [← hy_square] at hsquare
  exact (sq_le_sq₀ hx_nonneg hy_nonneg).mp hsquare

/-- The literal concentration scale is at least one on the constructor
parameter domain. -/
theorem one_le_rowConcentrationScale (p : ConstructorDimensions.Parameters) :
    1 ≤ rowConcentrationScale p := by
  have hm_one : (1 : ℝ) ≤ (p.m : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt (ConstructorDimensions.m_pos p)
  have hkt_one : (1 : ℝ) ≤ (p.K : ℝ) * (p.T : ℝ) :=
    ConstructorDimensions.KT_ge_one p
  have hb_one : (1 : ℝ) ≤ (b_N p : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt (ConstructorDimensions.b_N_pos p)
  have hsqrtm_one : 1 ≤ Real.sqrt (p.m : ℝ) :=
    (Real.one_le_sqrt).2 hm_one
  have hsqrtkt_one : 1 ≤ Real.sqrt ((p.K : ℝ) * (p.T : ℝ)) :=
    (Real.one_le_sqrt).2 hkt_one
  have hm_nonneg : 0 ≤ (p.m : ℝ) := Nat.cast_nonneg _
  have hsqrtm_nonneg : 0 ≤ Real.sqrt (p.m : ℝ) := Real.sqrt_nonneg _
  have hfirst_nonneg :
      0 ≤ (p.m : ℝ) * Real.sqrt (p.m : ℝ) :=
    mul_nonneg hm_nonneg hsqrtm_nonneg
  have hfirst_one :
      1 ≤ (p.m : ℝ) * Real.sqrt (p.m : ℝ) := by
    calc
      1 = 1 * 1 := by norm_num
      _ ≤ (p.m : ℝ) * Real.sqrt (p.m : ℝ) :=
        mul_le_mul hm_one hsqrtm_one zero_le_one hm_nonneg
  have hsecond_nonneg :
      0 ≤ (p.m : ℝ) * Real.sqrt (p.m : ℝ) *
        Real.sqrt ((p.K : ℝ) * (p.T : ℝ)) :=
    mul_nonneg hfirst_nonneg (Real.sqrt_nonneg _)
  have hsecond_one :
      1 ≤ (p.m : ℝ) * Real.sqrt (p.m : ℝ) *
        Real.sqrt ((p.K : ℝ) * (p.T : ℝ)) := by
    calc
      1 = 1 * 1 := by norm_num
      _ ≤ ((p.m : ℝ) * Real.sqrt (p.m : ℝ)) *
          Real.sqrt ((p.K : ℝ) * (p.T : ℝ)) :=
        mul_le_mul hfirst_one hsqrtkt_one zero_le_one hfirst_nonneg
  calc
    1 = 1 * 1 := by norm_num
    _ ≤ ((p.m : ℝ) * Real.sqrt (p.m : ℝ) *
        Real.sqrt ((p.K : ℝ) * (p.T : ℝ))) * (b_N p : ℝ) :=
      mul_le_mul hsecond_one hb_one zero_le_one hsecond_nonneg
    _ = rowConcentrationScale p := rfl

/-- The small-horizon complementary branch inherits the fixed-assignment
regret estimate at scale `sqrt(C_b) V`. The uniform constant appears before
the parameters and hence cannot depend on `K`, `m`, or `T`. -/
theorem bestFixedMSetComparator_regret_le_sqrt_constant_mul_rowConcentrationScale_of_horizon
    (C_b : ℝ) (hC_b : 0 ≤ C_b) (p : ConstructorDimensions.Parameters)
    (hT : (p.T : ℝ) ≤ C_b * (p.m : ℝ) * (p.K : ℝ) *
      (b_N p : ℝ) ^ 2)
    (rewards : RewardMatrix p.T p.K) {PublicData PrivateInput : Type*}
    (publicData : PublicData) (privateInput : Player p.m → PrivateInput) :
    bestFixedMSetComparator (ConstructorDimensions.m_pos p)
        (Nat.le_of_lt p.m_lt_K) rewards -
      pathwiseCumulativeReward
        (deterministicRollout
          (fixedAssignmentPolicy (Nat.le_of_lt p.m_lt_K))
          publicData privateInput rewards) ≤
      Real.sqrt C_b * rowConcentrationScale p := by
  calc
    _ ≤ (p.m : ℝ) * (p.T : ℝ) :=
      FixedAssignmentRegret.bestFixedMSetComparator_regret_le_m_mul_T
        (ConstructorDimensions.m_pos p) (Nat.le_of_lt p.m_lt_K) rewards
        publicData privateInput
    _ ≤ Real.sqrt C_b * rowConcentrationScale p :=
      m_mul_T_le_sqrt_constant_mul_rowConcentrationScale_of_horizon
        C_b hC_b p hT

/-- In the small-size case, the source dimension `N` bounds `m T`. The
argument uses the literal constructor definition `N = 2 K m (T+1)`. -/
theorem m_mul_T_le_N (p : ConstructorDimensions.Parameters) :
    (p.m : ℝ) * (p.T : ℝ) ≤ (N p : ℝ) := by
  have hK_one : 1 ≤ p.K := Nat.succ_le_of_lt (ConstructorDimensions.K_pos p)
  have hfactor : 1 ≤ 2 * p.K := by
    calc
      1 ≤ p.K := hK_one
      _ ≤ 2 * p.K := by
        have h := Nat.mul_le_mul_right p.K (by decide : 1 ≤ 2)
        simpa only [Nat.one_mul] using h
  have hproduct :
      1 * (p.m * (p.T + 1)) ≤ (2 * p.K) * (p.m * (p.T + 1)) :=
    Nat.mul_le_mul_right (p.m * (p.T + 1)) hfactor
  have hnatural : p.m * p.T ≤ N p := by
    change p.m * p.T ≤ 2 * p.K * p.m * (p.T + 1)
    calc
      p.m * p.T ≤ p.m * (p.T + 1) :=
        Nat.mul_le_mul_left p.m (Nat.le_add_right p.T 1)
      _ = 1 * (p.m * (p.T + 1)) := by simp
      _ ≤ (2 * p.K) * (p.m * (p.T + 1)) := hproduct
      _ = 2 * p.K * p.m * (p.T + 1) := by simp [Nat.mul_assoc]
  exact_mod_cast hnatural

/-- The small-size complementary branch absorbs the fixed-assignment regret
into `N₀ V`; the displayed `N₀` is uniform in the constructor parameters. -/
theorem bestFixedMSetComparator_regret_le_N0_mul_rowConcentrationScale_of_small_size
    (N0 : ℝ) (hN0 : 0 ≤ N0) (p : ConstructorDimensions.Parameters)
    (hN : (N p : ℝ) < N0)
    (rewards : RewardMatrix p.T p.K) {PublicData PrivateInput : Type*}
    (publicData : PublicData) (privateInput : Player p.m → PrivateInput) :
    bestFixedMSetComparator (ConstructorDimensions.m_pos p)
        (Nat.le_of_lt p.m_lt_K) rewards -
      pathwiseCumulativeReward
        (deterministicRollout
          (fixedAssignmentPolicy (Nat.le_of_lt p.m_lt_K))
          publicData privateInput rewards) ≤
      N0 * rowConcentrationScale p := by
  have hregret :=
    FixedAssignmentRegret.bestFixedMSetComparator_regret_le_m_mul_T
      (ConstructorDimensions.m_pos p) (Nat.le_of_lt p.m_lt_K) rewards
      publicData privateInput
  have hsmall : (p.m : ℝ) * (p.T : ℝ) ≤ N0 :=
    (m_mul_T_le_N p).trans hN.le
  have hscale_one := one_le_rowConcentrationScale p
  have hN0_scale : N0 ≤ N0 * rowConcentrationScale p := by
    calc
      N0 = N0 * 1 := by ring
      _ ≤ N0 * rowConcentrationScale p :=
        mul_le_mul_of_nonneg_left hscale_one hN0
  exact hregret.trans (hsmall.trans hN0_scale)

/-- On the negation of the two source construction-branch inequalities, the
same fixed constants `C_b` and `N₀` give one uniform fixed-assignment regret
bound. The larger of the two branch coefficients absorbs either case. -/
theorem bestFixedMSetComparator_regret_le_complementary_branch_mul_rowConcentrationScale
    (C_b N0 : ℝ) (hC_b : 0 ≤ C_b) (hN0 : 0 ≤ N0)
    (p : ConstructorDimensions.Parameters)
    (hComplement :
      ¬ (C_b * (p.m : ℝ) * (p.K : ℝ) * (b_N p : ℝ) ^ 2 < (p.T : ℝ) ∧
        N0 ≤ (N p : ℝ)))
    (rewards : RewardMatrix p.T p.K) {PublicData PrivateInput : Type*}
    (publicData : PublicData) (privateInput : Player p.m → PrivateInput) :
    bestFixedMSetComparator (ConstructorDimensions.m_pos p)
        (Nat.le_of_lt p.m_lt_K) rewards -
      pathwiseCumulativeReward
        (deterministicRollout
          (fixedAssignmentPolicy (Nat.le_of_lt p.m_lt_K))
          publicData privateInput rewards) ≤
      max (Real.sqrt C_b) N0 * rowConcentrationScale p := by
  by_cases hT : (p.T : ℝ) ≤
      C_b * (p.m : ℝ) * (p.K : ℝ) * (b_N p : ℝ) ^ 2
  · calc
      _ ≤ Real.sqrt C_b * rowConcentrationScale p :=
        bestFixedMSetComparator_regret_le_sqrt_constant_mul_rowConcentrationScale_of_horizon
          C_b hC_b p hT rewards publicData privateInput
      _ ≤ max (Real.sqrt C_b) N0 * rowConcentrationScale p :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (rowConcentrationScale_nonneg p)
  · have hT_large :
        C_b * (p.m : ℝ) * (p.K : ℝ) * (b_N p : ℝ) ^ 2 < (p.T : ℝ) :=
      lt_of_not_ge hT
    have hN_small : (N p : ℝ) < N0 := by
      by_contra hnot
      exact hComplement ⟨hT_large, le_of_not_gt hnot⟩
    calc
      _ ≤ N0 * rowConcentrationScale p :=
        bestFixedMSetComparator_regret_le_N0_mul_rowConcentrationScale_of_small_size
          N0 hN0 p hN_small rewards publicData privateInput
      _ ≤ max (Real.sqrt C_b) N0 * rowConcentrationScale p :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (rowConcentrationScale_nonneg p)

end Bandits.Support.SmallRegimeAbsorption

end
