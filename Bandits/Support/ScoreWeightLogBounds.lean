module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic

import Bandits.Support.ScoreWeights
import Mathlib.Tactic.Linarith

/-!
Logarithmic bounds for the slow/fast learner's score-weight base
`1 + 1 / D`. These are scalar inputs to the later potential telescope, not
the full learning bound. Source: `sources/zip4/manuscript/04_slow_fast_learner.tex:140-174`
and `:395-452`.
-/

public section

namespace Bandits.Support.ScoreWeightLogBounds

/-- The denominator `D + 1` in the lower bound is positive for positive `D`.
Source: `sources/zip4/manuscript/04_slow_fast_learner.tex:395-401`. -/
theorem source_denominator_pos {D : ℝ} (hD : 0 < D) : 0 < D + 1 := by
  exact add_pos hD zero_lt_one

/-- The source weight base has logarithm at least `1 / (D + 1)`.
Source: `sources/zip4/manuscript/04_slow_fast_learner.tex:140-145, 395-401`. -/
theorem source_base_log_lower {D : ℝ} (hD : 0 < D) :
    1 / (D + 1) ≤ Real.log (1 + 1 / D) := by
  have hInv : 0 < 1 / D := one_div_pos.mpr hD
  have hInner : 0 < 1 / D + 2 := by positivity
  have hLibrary : 2 * (1 / D) / (1 / D + 2) ≤ Real.log (1 + 1 / D) :=
    Real.le_log_one_add_of_nonneg hInv.le
  have hFraction : 1 / (D + 1) ≤ 2 * (1 / D) / (1 / D + 2) := by
    rw [div_le_div_iff₀ (source_denominator_pos hD) hInner]
    have hCancel : D * (1 / D) = 1 := by
      simpa only [one_div] using mul_inv_cancel₀ hD.ne'
    nlinarith [hCancel]
  exact hFraction.trans hLibrary

/-- The source weight base has logarithm at most `1 / D`.
Source: `sources/zip4/manuscript/04_slow_fast_learner.tex:140-145, 395-401`. -/
theorem source_base_log_upper {D : ℝ} (hD : 0 < D) :
    Real.log (1 + 1 / D) ≤ 1 / D := by
  calc
    Real.log (1 + 1 / D) ≤ (1 + 1 / D) - 1 :=
      Real.log_le_sub_one_of_pos (Bandits.Support.ScoreWeights.sourceBase_pos hD)
    _ = 1 / D := by rw [add_sub_cancel_left]

/-- The logarithm of the `k`-step score-weight factor is at most `k / D`.
The equality `Real.log (b ^ k) = k * Real.log b` is Mathlib's
`Real.log_pow`; this bound uses that identity and the preceding base bound.
Source: `sources/zip4/manuscript/04_slow_fast_learner.tex:395-401`. -/
theorem source_base_log_pow_le {D : ℝ} (hD : 0 < D) (k : ℕ) :
    Real.log ((1 + 1 / D) ^ k) ≤ (k : ℝ) / D := by
  calc
    Real.log ((1 + 1 / D) ^ k) = (k : ℝ) * Real.log (1 + 1 / D) :=
      Real.log_pow _ _
    _ ≤ (k : ℝ) * (1 / D) :=
      mul_le_mul_of_nonneg_left (source_base_log_upper hD) (Nat.cast_nonneg k)
    _ = (k : ℝ) / D := by simp only [div_eq_mul_inv, one_mul]

end Bandits.Support.ScoreWeightLogBounds

end
