module

public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

import Mathlib.Tactic.Linarith

/-!
Helpers for rounding real rewards down to a denominator grid.

Source: `sources/zip4/manuscript/08_main_theorem.tex:140-176`, especially
lines 163-168, states that rounding down loses at most `m / D` in a comparator
reward in each round.
This module proves the scalar floor estimate and its finite-sum consequence;
it does not establish that an algorithm's actions agree on the two reward
matrices.
-/

public section

namespace Bandits.Support.RewardRounding

/-- Round `r` down to the grid with spacing `1 / D`, using `Nat.floor`. -/
@[expose] noncomputable def rounded (D : ℕ) (r : ℝ) : ℝ :=
  (Nat.floor ((D : ℝ) * r) : ℝ) / (D : ℝ)

theorem rounded_nonneg (D : ℕ) (r : ℝ) : 0 ≤ rounded D r := by
  unfold rounded
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem rounded_le (D : ℕ) (r : ℝ) (hD : 0 < D) (hr : 0 ≤ r) :
    rounded D r ≤ r := by
  have hD' : 0 < (D : ℝ) := Nat.cast_pos.mpr hD
  unfold rounded
  apply (div_le_iff₀ hD').2
  simpa [mul_comm] using Nat.floor_le (mul_nonneg (Nat.cast_nonneg D) hr)

theorem rounded_mem_unitInterval (D : ℕ) (r : ℝ) (hD : 0 < D)
    (hr : r ∈ Set.Icc (0 : ℝ) 1) : rounded D r ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact rounded_nonneg D r
  · exact (rounded_le D r hD hr.1).trans hr.2

theorem sub_rounded_lt_inv (D : ℕ) (r : ℝ) (hD : 0 < D) :
    r - rounded D r < 1 / (D : ℝ) := by
  have hD' : 0 < (D : ℝ) := Nat.cast_pos.mpr hD
  have hfloor : (D : ℝ) * r < (Nat.floor ((D : ℝ) * r) : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have hgap : (D : ℝ) * r - (Nat.floor ((D : ℝ) * r) : ℝ) < 1 := by
    linarith
  unfold rounded
  calc
    r - (Nat.floor ((D : ℝ) * r) : ℝ) / (D : ℝ) =
        (r * (D : ℝ)) / (D : ℝ) - (Nat.floor ((D : ℝ) * r) : ℝ) / (D : ℝ) := by
          rw [mul_div_cancel_right₀ r hD'.ne']
    _ = (r * (D : ℝ) - (Nat.floor ((D : ℝ) * r) : ℝ)) / (D : ℝ) := by
          rw [← sub_div]
    _ = ((D : ℝ) * r - (Nat.floor ((D : ℝ) * r) : ℝ)) / (D : ℝ) := by
          rw [mul_comm]
    _ < 1 / (D : ℝ) := div_lt_div_of_pos_right hgap hD'

/-- If every summand is bounded above by `ε`, their finite sum is at most
`card(s) * ε`. -/
theorem sum_error_le_card_mul {α : Type*} (s : Finset α) (f g : α → ℝ)
    (ε : ℝ) (h : ∀ i ∈ s, f i - g i ≤ ε) :
    (∑ i ∈ s, (f i - g i)) ≤ (s.card : ℝ) * ε := by
  calc
    (∑ i ∈ s, (f i - g i)) ≤ ∑ i ∈ s, ε := by
      exact Finset.sum_le_sum (fun i hi => h i hi)
    _ = (s.card : ℝ) * ε := by simp

/-- If each summand is strictly below `1 / D`, their finite sum is at most
the non-strict bound `card(s) / D`. -/
theorem sum_error_le_card_div {α : Type*} (s : Finset α) (D : ℕ)
    (f g : α → ℝ)
    (h : ∀ i ∈ s, f i - g i < 1 / (D : ℝ)) :
    (∑ i ∈ s, (f i - g i)) ≤ (s.card : ℝ) / (D : ℝ) := by
  have hsum := sum_error_le_card_mul s f g (1 / (D : ℝ))
    (fun i hi => (h i hi).le)
  simpa [div_eq_mul_inv] using hsum

end Bandits.Support.RewardRounding
