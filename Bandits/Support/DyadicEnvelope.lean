module

public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
Dyadic rounding for positive real recording rates.

Source: `sources/zip4/manuscript/04_slow_fast_learner.tex:96-138`, especially
the definition of `xi_i` in lines 111-113 and its rounding bounds in lines
127-138.  The exponent below is the integer ceiling `Int.ceil (Real.logb 2 x)`;
we cast that integer to `ℝ` and use `Real.rpow`.  By `Real.rpow_intCast`, this
agrees with the real `zpow` convention for an integral exponent, including
negative exponents.
-/

public section

namespace Bandits.Support.DyadicEnvelope

/-- The least dyadic power at or above `x`, using the integer ceiling of
`log₂ x` and interpreting its exponent through `Real.rpow`. -/
@[expose] noncomputable def dyadicCeiling (x : ℝ) : ℝ :=
  (2 : ℝ) ^ (Int.ceil (Real.logb 2 x) : ℝ)

/-- For positive `x`, its dyadic ceiling lies in `[x, 2x)`. -/
theorem dyadicCeiling_bounds {x : ℝ} (hx : 0 < x) :
    x ≤ dyadicCeiling x ∧ dyadicCeiling x < 2 * x := by
  constructor
  · change x ≤ (2 : ℝ) ^ (Int.ceil (Real.logb 2 x) : ℝ)
    exact (Real.logb_le_iff_le_rpow one_lt_two hx).mp (Int.le_ceil _)
  · change (2 : ℝ) ^ (Int.ceil (Real.logb 2 x) : ℝ) < 2 * x
    have hceil : (Int.ceil (Real.logb 2 x) : ℝ) < Real.logb 2 x + 1 :=
      Int.ceil_lt_add_one _
    calc
      (2 : ℝ) ^ (Int.ceil (Real.logb 2 x) : ℝ) <
          (2 : ℝ) ^ (Real.logb 2 x + 1) :=
        Real.rpow_lt_rpow_of_exponent_lt one_lt_two hceil
      _ = 2 * x := by
        rw [Real.rpow_add_one (ne_of_gt zero_lt_two),
          Real.rpow_logb zero_lt_two (ne_of_gt one_lt_two) hx, mul_comm]

/-- The manuscript's `max (β, f)` rate is at least both inputs and strictly
less than twice their maximum whenever `β` is positive. -/
theorem dyadicCeiling_max_bounds {beta f : ℝ} (hbeta : 0 < beta) :
    beta ≤ dyadicCeiling (max beta f) ∧
      f ≤ dyadicCeiling (max beta f) ∧
      dyadicCeiling (max beta f) < 2 * max beta f := by
  have hmax : 0 < max beta f := hbeta.trans_le (le_max_left beta f)
  obtain ⟨hlo, hhi⟩ := dyadicCeiling_bounds hmax
  exact ⟨(le_max_left beta f).trans hlo,
    (le_max_right beta f).trans hlo, hhi⟩

end Bandits.Support.DyadicEnvelope
