/-
Copyright (c) 2026 Bandits contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.RewardMatrixCount
public import Mathlib.Logic.Equiv.Set

/-!
# Cardinality of the explicit real reward grid

The manuscript counts denominator-`D` matrices in the whole-row concentration
argument (`sources/zip4/manuscript/08_main_theorem.tex:26-65`) and later uses a
rounding comparison for arbitrary original matrices
(`sources/zip4/manuscript/08_main_theorem.tex:163-168`). This module defines the
real set obtained from `k ↦ (k : ℝ) / D` for `k : Fin (D + 1)` and proves its
table count by an explicit equivalence with the existing `Fin` encoding. It
does not identify arbitrary manuscript reward matrices with this set.
-/

@[expose] public section

namespace Bandits.Support.RealRewardGridCount

/-- The real value represented by a grid index `k` at positive denominator `D`. -/
noncomputable def realRewardGridValue (D : ℕ) (_hD : 0 < D) (k : Fin (D + 1)) : ℝ :=
  (k : ℝ) / (D : ℝ)

/-- The real denominator-`D` grid, defined as the image of its `Fin (D + 1)` indices. -/
def realRewardGrid (D : ℕ) (hD : 0 < D) : Set ℝ :=
  Set.range (realRewardGridValue D hD)

/-- Distinct indices give distinct real grid values when the denominator is positive. -/
theorem realRewardGridValue_injective (D : ℕ) (hD : 0 < D) :
    Function.Injective (realRewardGridValue D hD) := by
  intro a b hab
  apply Fin.ext
  have hDpos : 0 < (D : ℝ) := by exact_mod_cast hD
  have hcast : (a : ℝ) = (b : ℝ) :=
    (div_left_inj' (ne_of_gt hDpos)).mp hab
  exact_mod_cast hcast

/-- Every real grid value lies in the unit interval. -/
theorem realRewardGridValue_mem_Icc (D : ℕ) (hD : 0 < D) (k : Fin (D + 1)) :
    realRewardGridValue D hD k ∈ Set.Icc (0 : ℝ) 1 := by
  have hDpos : 0 < (D : ℝ) := by exact_mod_cast hD
  have hk : k.val ≤ D := Nat.lt_succ_iff.mp k.isLt
  constructor
  · have hk_nonneg : (0 : ℝ) ≤ (k.val : ℝ) := by exact_mod_cast Nat.zero_le k.val
    exact div_nonneg hk_nonneg (le_of_lt hDpos)
  · rw [realRewardGridValue, div_le_one hDpos]
    exact_mod_cast hk

/-- Indices are equivalent to the subtype of real values in the grid image.

The inverse comes from the injective map into its range, so every subtype value
has exactly one index. -/
noncomputable def realRewardGridIndexEquiv (D : ℕ) (hD : 0 < D) :
    Fin (D + 1) ≃ realRewardGrid D hD :=
  Equiv.ofInjective (realRewardGridValue D hD) (realRewardGridValue_injective D hD)

/-- The grid subtype is finite, with its enumeration given by the proved index equivalence. -/
noncomputable instance realRewardGridFintype (D : ℕ) (hD : 0 < D) :
    Fintype (realRewardGrid D hD) :=
  Fintype.ofEquiv (Fin (D + 1)) (realRewardGridIndexEquiv D hD)

/-- The pointwise equivalence from Fin-coded reward tables to real-grid tables. -/
noncomputable def realRewardMatrixEncodingEquiv (D K T : ℕ) (hD : 0 < D) :
    (Fin T → Fin K → Fin (D + 1)) ≃ (Fin T → Fin K → realRewardGrid D hD) :=
  Equiv.piCongrRight fun _ =>
    Equiv.piCongrRight fun _ => realRewardGridIndexEquiv D hD

/-- There are exactly `(D + 1)^(K*T)` functions with entries in the real grid. -/
theorem realRewardMatrixCount (D K T : ℕ) (hD : 0 < D) :
    Fintype.card (Fin T → Fin K → realRewardGrid D hD) = (D + 1) ^ (K * T) := by
  classical
  calc
    Fintype.card (Fin T → Fin K → realRewardGrid D hD) =
        Fintype.card (Fin T → Fin K → Fin (D + 1)) :=
      Fintype.card_congr (realRewardMatrixEncodingEquiv D K T hD).symm
    _ = (D + 1) ^ (K * T) :=
      Bandits.Support.RewardMatrixCount.rewardMatrixCount D K T

end Bandits.Support.RealRewardGridCount

end
