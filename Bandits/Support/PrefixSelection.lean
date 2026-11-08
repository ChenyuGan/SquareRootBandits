module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
Arithmetic for deterministic prefix selection. Source:
`sources/zip4/manuscript/appendix_a_local_protocol.tex:66-77`.
These lemmas concern prefix masses and threshold comparisons only.
-/

public section

namespace Bandits.Support.PrefixSelection

/-- A prefix mass divided by the total mass lies in the unit interval. -/
theorem prefixProbability_mem_unitInterval {W Win : ℝ} (hW : 0 < W)
    (hWin_nonneg : 0 ≤ Win) (hWin_le : Win ≤ W) :
    0 ≤ Win / W ∧ Win / W ≤ 1 := by
  constructor
  · exact div_nonneg hWin_nonneg hW.le
  · exact (div_le_one hW).2 hWin_le

/-- The two branches of the prefix threshold test each leave positive mass.

The rejection hypothesis is the complement of the strict acceptance test, so
it includes the equality boundary `Win = v * W`.
-/
theorem prefixBranchHasPositiveMass {W Win v : ℝ} (hW : 0 < W)
    (hv_nonneg : 0 ≤ v) (hv_lt_one : v < 1) :
    (Win > v * W → 0 < Win) ∧ (¬ Win > v * W → 0 < W - Win) := by
  constructor
  · intro hAccept
    exact lt_of_le_of_lt (mul_nonneg hv_nonneg hW.le) hAccept
  · intro hReject
    have hWin_le_threshold : Win ≤ v * W := le_of_not_gt hReject
    have hPositive_remainder : 0 < W - v * W := by
      calc
        0 < (1 - v) * W := mul_pos (sub_pos.mpr hv_lt_one) hW
        _ = W - v * W := by rw [sub_mul, one_mul]
    exact lt_of_lt_of_le hPositive_remainder
      (sub_le_sub_left hWin_le_threshold W)

end Bandits.Support.PrefixSelection
