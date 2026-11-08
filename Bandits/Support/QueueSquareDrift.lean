module

public import Mathlib.Basic.Real.Basic

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Deterministic queue square drift

These scalar helpers formalize the deterministic queue inequalities used in
`sources/zip4/manuscript/04_slow_fast_learner.tex:299-305`. The weighted
comparison formalizes the preceding one-step weight bound at lines 292-297.
They do not assert a stochastic moment law or close the manuscript's weighted
backlog argument.
-/

public section

namespace Bandits.Support.QueueSquareDrift

/-- One application of the queue recursion with service amount `4`. -/
@[expose] def queueNext (b r : ℝ) : ℝ := max 0 (b + r - 4)

/-- The queue recursion gives the square drift bound from the manuscript. -/
theorem queueNext_sq_sub_le (b r : ℝ) (_hb : 0 ≤ b) (hr : 0 ≤ r) :
    queueNext b r ^ 2 - b ^ 2 ≤ 2 * b * (r - 4) + r ^ 2 + 16 := by
  unfold queueNext
  by_cases h : 0 ≤ b + r - 4
  · rw [max_eq_right h]
    nlinarith
  · rw [max_eq_left (le_of_not_ge h)]
    nlinarith [sq_nonneg (b + r - 4)]

/-- The next queue cannot exceed the previous queue plus the arrival. -/
theorem queueNext_le_add (b r : ℝ) (hb : 0 ≤ b) (hr : 0 ≤ r) :
    queueNext b r ≤ b + r := by
  unfold queueNext
  apply max_le
  · exact add_nonneg hb hr
  · linarith

/-- If the next queue is capped by `2 * B`, its square is bounded by the
cap times the previous queue plus the arrival. -/
theorem queueNext_sq_le_cap_mul (b r B : ℝ)
    (hb : 0 ≤ b) (hr : 0 ≤ r) (_hB : 0 ≤ B)
    (hcap : queueNext b r ≤ 2 * B) :
    queueNext b r ^ 2 ≤ 2 * B * (b + r) := by
  have hnext_nonneg : 0 ≤ queueNext b r := by
    unfold queueNext
    exact le_max_left 0 (b + r - 4)
  have hnext_le_add := queueNext_le_add b r hb hr
  have hadd_nonneg : 0 ≤ b + r := add_nonneg hb hr
  calc
    queueNext b r ^ 2 = queueNext b r * queueNext b r := by ring
    _ ≤ queueNext b r * (b + r) :=
      mul_le_mul_of_nonneg_left hnext_le_add hnext_nonneg
    _ ≤ (2 * B) * (b + r) :=
      mul_le_mul_of_nonneg_right hcap hadd_nonneg

/-- A multiplicative coordinate-weight increase gives the corresponding
weighted square comparison. -/
theorem weighted_square_step
    (thetaNext theta eta bNext b : ℝ)
    (_htheta : 0 ≤ theta) (_heta : 0 ≤ eta)
    (hweight : thetaNext ≤ (1 + 8 * eta) * theta) :
    thetaNext * bNext ^ 2 - theta * b ^ 2 ≤
      theta * (bNext ^ 2 - b ^ 2 + 8 * eta * bNext ^ 2) := by
  calc
    thetaNext * bNext ^ 2 - theta * b ^ 2 ≤
        ((1 + 8 * eta) * theta) * bNext ^ 2 - theta * b ^ 2 := by
      exact sub_le_sub_right
        (mul_le_mul_of_nonneg_right hweight (sq_nonneg bNext)) _
    _ = theta * (bNext ^ 2 - b ^ 2 + 8 * eta * bNext ^ 2) := by ring

end Bandits.Support.QueueSquareDrift
