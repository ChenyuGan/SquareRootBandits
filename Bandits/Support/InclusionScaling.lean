module
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic

/-! Internal arithmetic helpers motivated by the inclusion scaling step in
`sources/zip4/manuscript/04_slow_fast_learner.tex`, raw lines 89–90.
The finite-mass comparison abstracts the same factor-two normalization
argument from raw lines 25–37 and 89–90. These are internal helpers, not a
formalization of the manuscript lemma. -/

public section

namespace Bandits.Support.InclusionScaling

theorem denominator_pos {θ c : ℝ} (hθ_nonneg : 0 ≤ θ) (hc : 1 ≤ c) :
    0 < 1 + (c - 1) * θ := by
  have hterm : 0 ≤ (c - 1) * θ :=
    mul_nonneg (sub_nonneg.mpr hc) hθ_nonneg
  exact add_pos_of_pos_of_nonneg zero_lt_one hterm

theorem scaled_inclusion_le_scaled {θ c : ℝ} (hθ_nonneg : 0 ≤ θ)
    (hc : 1 ≤ c) :
    c * θ / (1 + (c - 1) * θ) ≤ c * θ := by
  have hnum : 0 ≤ c * θ := mul_nonneg (le_trans zero_le_one hc) hθ_nonneg
  have hden : 1 ≤ 1 + (c - 1) * θ :=
    le_add_of_nonneg_right (mul_nonneg (sub_nonneg.mpr hc) hθ_nonneg)
  exact div_le_self hnum hden

theorem scaled_inclusion_mem_Icc {θ c : ℝ} (hθ_nonneg : 0 ≤ θ)
    (hθ_le_one : θ ≤ 1) (hc : 1 ≤ c) :
    c * θ / (1 + (c - 1) * θ) ∈ Set.Icc 0 1 := by
  have hden : 0 < 1 + (c - 1) * θ := denominator_pos hθ_nonneg hc
  have hnum : 0 ≤ c * θ := mul_nonneg (le_trans zero_le_one hc) hθ_nonneg
  refine ⟨div_nonneg hnum hden.le, ?_⟩
  apply (div_le_one hden).2
  have hc_eq : (c - 1) + 1 = c := sub_add_cancel c 1
  calc
    c * θ = (c - 1) * θ + θ := by
      calc
        c * θ = ((c - 1) + 1) * θ := congrArg (fun x => x * θ) hc_eq.symm
        _ = (c - 1) * θ + θ := by rw [add_mul, one_mul]
    _ ≤ (c - 1) * θ + 1 := add_le_add_right hθ_le_one ((c - 1) * θ)
    _ = 1 + (c - 1) * θ := add_comm _ _

/-- Replacing each nonnegative finite mass by a value between it and twice it
can reduce any normalized atom's mass by at most a factor of two. -/
theorem normalized_weight_factor_two {ι : Type*} (s : Finset ι)
    (v w : ι → ℝ) (i : ι) (hi : i ∈ s)
    (hv_nonneg : ∀ j ∈ s, 0 ≤ v j)
    (hv_le_w : ∀ j ∈ s, v j ≤ w j)
    (hw_le_two_v : ∀ j ∈ s, w j ≤ 2 * v j)
    (_hv_sum_pos : 0 < s.sum v) (hw_sum_pos : 0 < s.sum w) :
    (v i / s.sum v) / 2 ≤ w i / s.sum w := by
  have hsum : s.sum w ≤ 2 * s.sum v := by
    calc
      s.sum w ≤ s.sum (fun j => 2 * v j) :=
        Finset.sum_le_sum fun j hj => hw_le_two_v j hj
      _ = 2 * s.sum v := by rw [Finset.mul_sum]
  have hscaled : (2 * v i) / (2 * s.sum v) ≤ (2 * w i) / s.sum w :=
    div_le_div₀ (mul_nonneg (by norm_num)
        (le_trans (hv_nonneg i hi) (hv_le_w i hi)))
      (mul_le_mul_of_nonneg_left (hv_le_w i hi) (by norm_num))
      hw_sum_pos hsum
  have hscaled' : v i / s.sum v ≤ (2 * w i) / s.sum w := by
    simpa only [mul_div_mul_left _ _ (by norm_num : (2 : ℝ) ≠ 0)] using hscaled
  have hnormalized : v i / s.sum v ≤ 2 * (w i / s.sum w) := by
    simpa only [mul_div_assoc] using hscaled'
  exact (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).2 (by
    simpa only [mul_comm] using hnormalized)

end Bandits.Support.InclusionScaling
