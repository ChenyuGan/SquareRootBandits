module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Field.Basic

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Algebraic helpers for the inverse-anchor orientation of a weighted set. -/

public section

namespace Bandits.Support.OrientationAlgebra

/-- Reciprocal-anchor normalization used in the orientation formula.

Source: `sources/zip4/manuscript/04_slow_fast_learner.tex`, lines 30–34. -/
theorem inverse_anchor_normalization {α : Type*} [Field α] [LinearOrder α]
    [IsStrictOrderedRing α]
    {v s : α} (hv : 0 < v) (hs : 0 ≤ s) :
    (1 / v) / (s + 1 / v) = 1 / (1 + s * v) := by
  have hv0 : v ≠ 0 := ne_of_gt hv
  have hleft : s + 1 / v ≠ 0 :=
    ne_of_gt (add_pos_of_nonneg_of_pos hs (one_div_pos.mpr hv))
  have hright : 1 + s * v ≠ 0 :=
    ne_of_gt (add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg hs hv.le))
  field_simp [hv0, hleft, hright]
  ring

/-- The reweighted fast-arm mass is positive when the current weight is positive.

Source: `sources/zip4/manuscript/04_slow_fast_learner.tex`, equation (q), lines 25–28. -/
theorem current_weight_over_anchor_factor_pos {α : Type*} [Field α] [LinearOrder α]
    [IsStrictOrderedRing α]
    {w v s : α} (hw : 0 < w) (hv : 0 < v) (hs : 0 ≤ s) :
    0 < w / (1 + s * v) := by
  apply div_pos hw
  exact add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg hs hv.le)

/-- Multiplying the product mass on `U ∪ {j}` by the reciprocal-anchor orientation
probability cancels the anchor reciprocal and leaves the `j`-weight divided by its
normalizing factor.  The factor `s` may be instantiated by the inverse-anchor sum
over `U` in the source construction.

Source: `sources/zip4/manuscript/04_slow_fast_learner.tex`, lines 30–35. -/
theorem product_mass_union_orientation_cancel
    {ι : Type*} [DecidableEq ι] {α : Type*} [Field α] [LinearOrder α]
    [IsStrictOrderedRing α]
    (U : Finset ι) (j : ι) (w v : ι → α) (s : α)
    (hj : j ∉ U) (hv : 0 < v j) (hs : 0 ≤ s) :
    (∏ i ∈ U ∪ {j}, w i) * ((1 / v j) / (s + 1 / v j))
      = (∏ i ∈ U, w i) * (w j / (1 + s * v j)) := by
  have h_union : U ∪ {j} = insert j U := by
    ext i
    simp
  rw [h_union, Finset.prod_insert hj, inverse_anchor_normalization hv hs]
  ring

end Bandits.Support.OrientationAlgebra
