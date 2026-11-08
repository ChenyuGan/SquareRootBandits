module
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring

/-!
Algebraic monotonicity for the linear-over-linear odds expression in
`04_slow_fast_learner.tex:84-88`. The curvature inequality is an explicit input;
this module does not prove Newton's inequality or identify its coefficients.
-/
public section

namespace Bandits.Support.MarginalRatio

/-- The cross-product difference for the odds expression factors as the
parameter difference times the curvature difference.

Source: `sources/zip4/manuscript/04_slow_fast_learner.tex:84-88`.
-/
theorem crossProduct_sub_eq (A B C x y : ℝ) :
    (A + x * B) * (C + y * A) - (A + y * B) * (C + x * A) =
      (y - x) * (A ^ 2 - B * C) := by
  ring

/-- Under nonnegative curvature and positive denominators, the odds expression
is nonincreasing in the parameter. The curvature premise is an explicit
hypothesis, corresponding to the algebraic input supplied by Newton's
inequalities in the source discussion.

Source: `sources/zip4/manuscript/04_slow_fast_learner.tex:84-88`.
-/
theorem ratio_antitone (A B C x y : ℝ) (hxy : x ≤ y)
    (hcurv : A ^ 2 ≥ B * C) (hx : 0 < C + x * A) (hy : 0 < C + y * A) :
    (A + y * B) / (C + y * A) ≤ (A + x * B) / (C + x * A) := by
  rw [div_le_div_iff₀ hy hx]
  have hfactor : 0 ≤ (y - x) * (A ^ 2 - B * C) :=
    mul_nonneg (sub_nonneg.mpr hxy) (sub_nonneg.mpr hcurv)
  rw [← sub_nonneg, crossProduct_sub_eq]
  exact hfactor

end Bandits.Support.MarginalRatio
