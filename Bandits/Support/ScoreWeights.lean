module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Order.Field.Basic

/-!
Helpers for the integer score weights used by the slow/fast learner.

The source defines the weight as `(1 + 1 / D) ^ z` for an integer score `z`;
these lemmas record how that weight changes under score addition. Source:
`sources/zip4/manuscript/04_slow_fast_learner.tex:139-172`.
-/

public section

namespace Bandits.Support.ScoreWeights

/-- The multiplicative weight attached to a natural-number score. -/
@[expose] def scoreWeight (b : ℝ) (z : ℕ) : ℝ := b ^ z

/-- Adding scores multiplies their weights. -/
theorem scoreWeight_add (b : ℝ) (z k : ℕ) :
    scoreWeight b (z + k) = scoreWeight b z * scoreWeight b k := by
  simp only [scoreWeight, pow_add]

/-- A score weight is positive whenever its base is positive. -/
theorem scoreWeight_pos {b : ℝ} (hb : 0 < b) (z : ℕ) :
    0 < scoreWeight b z := by
  exact pow_pos hb z

/-- Score weights are monotone in the score when the base is at least one. -/
theorem scoreWeight_mono {b : ℝ} (hb : 1 ≤ b) {z k : ℕ} (hzk : z ≤ k) :
    scoreWeight b z ≤ scoreWeight b k := by
  exact pow_le_pow_right₀ hb hzk

/-- The exact multiplicative ratio caused by adding `k` to a score. -/
theorem scoreWeight_update_ratio {b : ℝ} (hb : 0 < b) (z k : ℕ) :
    scoreWeight b (z + k) / scoreWeight b z = scoreWeight b k := by
  rw [scoreWeight_add]
  exact mul_div_cancel_left₀ _ (scoreWeight_pos hb z).ne'

/-- The manuscript's base `(1 + 1 / D)` is at least one for positive `D`. -/
theorem sourceBase_one_le {D : ℝ} (hD : 0 < D) : 1 ≤ 1 + 1 / D := by
  have hInv : 0 < 1 / D := one_div_pos.mpr hD
  exact le_add_of_nonneg_right hInv.le

/-- The manuscript's base is positive for positive `D`. -/
theorem sourceBase_pos {D : ℝ} (hD : 0 < D) : 0 < 1 + 1 / D := by
  have hInv : 0 < 1 / D := one_div_pos.mpr hD
  exact add_pos_of_pos_of_nonneg zero_lt_one hInv.le

/-- Source weights are monotone as their integer score increases. -/
theorem sourceWeight_mono {D : ℝ} (hD : 0 < D) {z k : ℕ} (hzk : z ≤ k) :
    scoreWeight (1 + 1 / D) z ≤ scoreWeight (1 + 1 / D) k := by
  exact scoreWeight_mono (sourceBase_one_le hD) hzk

/-- The manuscript's weight ratio after a score update is exactly the update factor. -/
theorem sourceWeight_update_ratio {D : ℝ} (hD : 0 < D) (z k : ℕ) :
    scoreWeight (1 + 1 / D) (z + k) / scoreWeight (1 + 1 / D) z =
      (1 + 1 / D) ^ k := by
  simpa only [scoreWeight] using
    scoreWeight_update_ratio (sourceBase_pos hD) z k

end Bandits.Support.ScoreWeights
