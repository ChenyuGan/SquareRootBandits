/-
Copyright (c) 2026 The Bandits Lean regret formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ProductSetLaw
import Bandits.Support.ElementarySymmetricRatioMonotonicity
import Bandits.Support.InclusionCoordinateScaling
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Stability of canonical product-set inclusion marginals

This module proves that the inclusion marginal of the canonical product-set
law cannot increase when only the other coordinates are raised, proves its
exact own-coordinate rescaling formula, and combines these facts into the
factor-two marginal bound. The mathematical statements follow
`sources/zip4/manuscript/04_slow_fast_learner.tex:39-46,84-89`.

## Main results

- `theta_antitone_of_other_coord_le`: increasing coordinates other than the
  queried arm cannot increase its canonical inclusion marginal.
- `theta_update_eq`: the exact marginal after multiplying the queried weight.
- `theta_update_le`: the corresponding upper bound by the coordinate factor.
- `theta_le_two_of_coordinatewise_le_two`: the canonical factor-two bound.

These are internal mathematical results. They do not establish the separate
conditional-marginal, recording-rate, or regret conclusions.
-/

public section

open scoped BigOperators

namespace Bandits.Support.ProductMarginalStability

open Bandits.Support.ElementarySymmetricRecurrence

private theorem erased_sum_eq_elementary_symmetric {K : ℕ} (w : Fin K → ℝ)
    (i : Fin K) (k : ℕ) :
    (∑ T ∈ (Finset.univ.erase i).powersetCard k,
      Bandits.Support.ProductSetLaw.setWeight w T) =
        elementarySymmetric w (Finset.univ.erase i) k := rfl

private theorem theta_odds_eq_erased_ratio {K m : ℕ} (w : Fin K → ℝ) (i : Fin K)
    (hm : 0 < m) (hmK : m < K) (hw : ∀ j, 0 < w j) :
    Bandits.Support.ProductSetLaw.theta m w i /
        (1 - Bandits.Support.ProductSetLaw.theta m w i) =
      w i * (elementarySymmetric w (Finset.univ.erase i) (m - 1) /
        elementarySymmetric w (Finset.univ.erase i) m) := by
  have hi : i ∈ (Finset.univ : Finset (Fin K)) := Finset.mem_univ i
  have hcard : (Finset.univ.erase i).card = K - 1 := by
    rw [Finset.card_erase_of_mem hi]
    simp
  have hmle : m ≤ (Finset.univ.erase i).card := by omega
  have hsum_pos := elementarySymmetric_pos w (Finset.univ.erase i) m
    (fun j hj => hw j) hmle
  have hnormalizer_pos :=
    Bandits.Support.ProductSetLaw.normalizer_pos w hm hmK hw
  nth_rewrite 1 [Bandits.Support.ProductSetLaw.theta_eq_weight_mul_erased_sum_div w i hm]
  rw [Bandits.Support.ProductSetLaw.one_sub_theta_eq_erased_sum_div w i hm hmK hw,
    erased_sum_eq_elementary_symmetric w i (m - 1),
    erased_sum_eq_elementary_symmetric w i m]
  field_simp [ne_of_gt hnormalizer_pos, ne_of_gt hsum_pos]

/-- Increasing the weights away from `i`, while keeping its weight fixed,
weakly decreases the actual inclusion marginal of `i` under `ProductSetLaw`.

The proof applies the accepted elementary-symmetric ratio monotonicity theorem
on `Finset.univ.erase i` and uses the canonical erased numerator and
complement formulas for `theta`.

Source: `sources/zip4/manuscript/04_slow_fast_learner.tex:84-89`.
-/
theorem theta_antitone_of_other_coord_le {K m : ℕ} (v w : Fin K → ℝ)
    (i : Fin K) (hmlo : 2 ≤ m) (hmhi : m < K)
    (hvpos : ∀ j, 0 < v j) (hwpos : ∀ j, 0 < w j)
    (hown : v i = w i)
    (hother : ∀ j, j ≠ i → v j ≤ w j) :
    Bandits.Support.ProductSetLaw.theta m w i ≤
      Bandits.Support.ProductSetLaw.theta m v i := by
  have hm : 0 < m := by omega
  let J : Finset (Fin K) := Finset.univ.erase i
  have hi : i ∈ (Finset.univ : Finset (Fin K)) := Finset.mem_univ i
  have hcard : J.card = K - 1 := by
    dsimp [J]
    rw [Finset.card_erase_of_mem hi]
    simp
  have hmle : m ≤ J.card := by omega
  have hratio :=
    Bandits.Support.ElementarySymmetricRatioMonotonicity.elementary_symmetric_ratio_antitone
      J v w m hmlo hmle
      (fun j _ => hvpos j) (fun j _ => hwpos j)
      (fun j hj => hother j (Finset.mem_erase.mp hj).1)
  have hscaled := mul_le_mul_of_nonneg_left hratio (le_of_lt (hvpos i))
  have hodds :
      Bandits.Support.ProductSetLaw.theta m w i /
          (1 - Bandits.Support.ProductSetLaw.theta m w i) ≤
        Bandits.Support.ProductSetLaw.theta m v i /
          (1 - Bandits.Support.ProductSetLaw.theta m v i) := by
    calc
      _ = w i * (elementarySymmetric w J (m - 1) /
          elementarySymmetric w J m) := by
        exact theta_odds_eq_erased_ratio w i hm hmhi hwpos
      _ = v i * (elementarySymmetric w J (m - 1) /
          elementarySymmetric w J m) := by rw [hown]
      _ ≤ v i * (elementarySymmetric v J (m - 1) /
          elementarySymmetric v J m) := by
        exact hscaled
      _ = Bandits.Support.ProductSetLaw.theta m v i /
          (1 - Bandits.Support.ProductSetLaw.theta m v i) := by
        exact (theta_odds_eq_erased_ratio v i hm hmhi hvpos).symm
  have hden_w :=
    Bandits.Support.ProductSetLaw.one_sub_theta_pos w i hm hmhi hwpos
  have hden_v :=
    Bandits.Support.ProductSetLaw.one_sub_theta_pos v i hm hmhi hvpos
  have hcross := (div_le_div_iff₀ hden_w hden_v).mp hodds
  nlinarith [hcross]

private theorem setWeight_update_eq_if {K : ℕ} (v : Fin K → ℝ) (i : Fin K)
    (c : ℝ) (S : Finset (Fin K)) :
    Bandits.Support.ProductSetLaw.setWeight (Function.update v i (c * v i)) S =
      if i ∈ S then c * Bandits.Support.ProductSetLaw.setWeight v S
      else Bandits.Support.ProductSetLaw.setWeight v S := by
  classical
  by_cases hi : i ∈ S
  · rw [ite_eq_left hi]
    change (∏ j ∈ S, Function.update v i (c * v i) j) =
      c * (∏ j ∈ S, v j)
    rw [Finset.prod_update_of_mem hi v (c * v i)]
    calc
      c * v i * (∏ j ∈ S \ {i}, v j) =
          c * (v i * (∏ j ∈ S.erase i, v j)) := by
        rw [Finset.sdiff_singleton_eq_erase]
        ring
      _ = c * (∏ j ∈ S, v j) := by rw [Finset.mul_prod_erase S v hi]
  · rw [ite_eq_right hi]
    change (∏ j ∈ S, Function.update v i (c * v i) j) =
      ∏ j ∈ S, v j
    rw [Finset.prod_update_of_notMem hi v (c * v i)]

/-- The actual canonical marginal after a coordinate update has the exact
fractional rescaling formula. The proof identifies canonical product-set
weights with the finite rescaling of their normalized mass and then applies
`InclusionCoordinateScaling`.

Source: `sources/zip4/manuscript/04_slow_fast_learner.tex:84-89`.
-/
theorem theta_update_eq {K m : ℕ} (v : Fin K → ℝ) (i : Fin K) (c : ℝ)
    (hm : 0 < m) (hmK : m < K) (hvpos : ∀ j, 0 < v j) (hc : 1 ≤ c) :
    Bandits.Support.ProductSetLaw.theta m (Function.update v i (c * v i)) i =
      c * Bandits.Support.ProductSetLaw.theta m v i /
        (1 + (c - 1) * Bandits.Support.ProductSetLaw.theta m v i) := by
  classical
  let support := Bandits.Support.ProductSetLaw.support K m
  let included : Finset (Fin K) → Prop := fun S => i ∈ S
  let q : Finset (Fin K) → ℝ :=
    Bandits.Support.FiniteNormalization.normalizedWeight support
      (Bandits.Support.ProductSetLaw.setWeight v)
  let updated := Function.update v i (c * v i)
  have hcpos : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have hupdated_pos : ∀ j, 0 < updated j := by
    intro j
    by_cases hji : j = i
    · subst j
      simp only [updated, Function.update_self]
      exact mul_pos hcpos (hvpos i)
    · simp [updated, hji, hvpos]
  have hnormalizer_pos :=
    Bandits.Support.ProductSetLaw.normalizer_pos updated hm hmK hupdated_pos
  have hnormalizer_v_pos :=
    Bandits.Support.ProductSetLaw.normalizer_pos v hm hmK hvpos
  have hnormalized : (∑ S ∈ support, q S) = 1 := by
    dsimp [q, support]
    exact Bandits.Support.ProductSetLaw.total_mass_eq_one v hm hmK hvpos
  have hq (S : Finset (Fin K)) :
      q S = Bandits.Support.ProductSetLaw.setWeight v S /
        Bandits.Support.ProductSetLaw.normalizer m v := rfl
  have hrescaled_weight (S : Finset (Fin K)) :
      Bandits.Support.InclusionCoordinateScaling.rescaledWeight q included c S =
        Bandits.Support.ProductSetLaw.setWeight updated S /
          Bandits.Support.ProductSetLaw.normalizer m v := by
    rw [Bandits.Support.InclusionCoordinateScaling.rescaledWeight]
    change (if i ∈ S then c * q S else q S) = _
    rw [hq S, setWeight_update_eq_if]
    by_cases hi : i ∈ S
    · rw [ite_eq_left hi, ite_eq_left hi]
      ring
    · rw [ite_eq_right hi, ite_eq_right hi]
  have hnumerator :
      Bandits.Support.InclusionCoordinateScaling.rescaledInclusionMass
          support q included c =
        (∑ S ∈ support.filter included,
          Bandits.Support.ProductSetLaw.setWeight updated S) /
            Bandits.Support.ProductSetLaw.normalizer m v := by
    unfold Bandits.Support.InclusionCoordinateScaling.rescaledInclusionMass
    calc
      _ = ∑ S ∈ support.filter included,
          Bandits.Support.ProductSetLaw.setWeight updated S /
            Bandits.Support.ProductSetLaw.normalizer m v := by
        apply Finset.sum_congr rfl
        intro S hS
        exact hrescaled_weight S
      _ = _ := by rw [Finset.sum_div]
  have htotal :
      Bandits.Support.InclusionCoordinateScaling.rescaledTotalMass
          support q included c =
        Bandits.Support.ProductSetLaw.normalizer m updated /
          Bandits.Support.ProductSetLaw.normalizer m v := by
    unfold Bandits.Support.InclusionCoordinateScaling.rescaledTotalMass
    calc
      _ = ∑ S ∈ support,
          Bandits.Support.ProductSetLaw.setWeight updated S /
            Bandits.Support.ProductSetLaw.normalizer m v := by
        apply Finset.sum_congr rfl
        intro S hS
        exact hrescaled_weight S
      _ = (∑ S ∈ support, Bandits.Support.ProductSetLaw.setWeight updated S) /
          Bandits.Support.ProductSetLaw.normalizer m v := by rw [Finset.sum_div]
      _ = _ := by rw [← Bandits.Support.ProductSetLaw.normalizer_eq_support_sum]
  have htheta_updated :
      Bandits.Support.ProductSetLaw.theta m updated i =
        (∑ S ∈ support.filter included,
          Bandits.Support.ProductSetLaw.setWeight updated S) /
            Bandits.Support.ProductSetLaw.normalizer m updated := by
    unfold Bandits.Support.ProductSetLaw.theta
      Bandits.Support.FiniteNormalization.mass
      Bandits.Support.FiniteNormalization.normalizedWeight
    rw [← Finset.sum_div]
    rfl
  have hcanonical :
      Bandits.Support.ProductSetLaw.theta m updated i =
        Bandits.Support.InclusionCoordinateScaling.normalizedRescaledInclusionMass
          support q included c := by
    unfold Bandits.Support.InclusionCoordinateScaling.normalizedRescaledInclusionMass
    rw [hnumerator, htotal, htheta_updated]
    field_simp [ne_of_gt hnormalizer_pos, ne_of_gt hnormalizer_v_pos]
  have htheta_event :
      Bandits.Support.InclusionCoordinateScaling.inclusionMass support q included =
        Bandits.Support.ProductSetLaw.theta m v i := rfl
  have hformula :=
    Bandits.Support.InclusionCoordinateScaling.normalized_rescaled_inclusion_mass_eq
      support q included c hnormalized
  rw [htheta_event] at hformula
  exact hcanonical.trans hformula

/-- The coordinate-update marginal is bounded above by the coordinate factor
 times the original canonical marginal.

Source: `sources/zip4/manuscript/04_slow_fast_learner.tex:84-89`.
-/
theorem theta_update_le {K m : ℕ} (v : Fin K → ℝ) (i : Fin K) (c : ℝ)
    (hm : 0 < m) (hmK : m < K) (hvpos : ∀ j, 0 < v j) (hc : 1 ≤ c) :
    Bandits.Support.ProductSetLaw.theta m (Function.update v i (c * v i)) i ≤
      c * Bandits.Support.ProductSetLaw.theta m v i := by
  rw [theta_update_eq v i c hm hmK hvpos hc]
  have htheta_pos := Bandits.Support.ProductSetLaw.theta_pos v i hm hmK hvpos
  have hnum_nonneg : 0 ≤ c * Bandits.Support.ProductSetLaw.theta m v i :=
    mul_nonneg (le_of_lt (lt_of_lt_of_le zero_lt_one hc)) (le_of_lt htheta_pos)
  have hden :
      1 ≤ 1 + (c - 1) * Bandits.Support.ProductSetLaw.theta m v i := by
    nlinarith [le_of_lt htheta_pos, hc]
  have hden_pos :
      0 < 1 + (c - 1) * Bandits.Support.ProductSetLaw.theta m v i := by
    linarith
  apply (div_le_iff₀ hden_pos).2
  calc
    c * Bandits.Support.ProductSetLaw.theta m v i =
        (c * Bandits.Support.ProductSetLaw.theta m v i) * 1 := by ring
    _ ≤ (c * Bandits.Support.ProductSetLaw.theta m v i) *
        (1 + (c - 1) * Bandits.Support.ProductSetLaw.theta m v i) :=
      mul_le_mul_of_nonneg_left hden hnum_nonneg

/-- For positive weights with `v j ≤ w j ≤ 2 * v j`, the canonical
inclusion marginal is at most twice its original value.

The intermediate vector first replaces every coordinate other than `i`, then
an exact own-coordinate update completes the passage to `w`.

Source: `sources/zip4/manuscript/04_slow_fast_learner.tex:84-89`.
-/
theorem theta_le_two_of_coordinatewise_le_two {K m : ℕ} (v w : Fin K → ℝ)
    (i : Fin K) (hmlo : 2 ≤ m) (hmhi : m < K)
    (hvpos : ∀ j, 0 < v j) (hwpos : ∀ j, 0 < w j)
    (hbounds : ∀ j, v j ≤ w j ∧ w j ≤ 2 * v j) :
    Bandits.Support.ProductSetLaw.theta m w i ≤
      2 * Bandits.Support.ProductSetLaw.theta m v i := by
  let u := Function.update w i (v i)
  have hu_pos : ∀ j, 0 < u j := by
    intro j
    by_cases hji : j = i
    · subst j
      simp [u, hvpos i]
    · simp [u, hji, hwpos]
  have huown : v i = u i := by simp [u]
  have huother : ∀ j, j ≠ i → v j ≤ u j := by
    intro j hji
    simpa [u, hji] using (hbounds j).1
  have hmonotone := theta_antitone_of_other_coord_le v u i hmlo hmhi
    hvpos hu_pos huown huother
  let c : ℝ := w i / v i
  have hc : 1 ≤ c := by
    dsimp [c]
    rw [le_div_iff₀ (hvpos i)]
    simpa using (hbounds i).1
  have hc2 : c ≤ 2 := by
    dsimp [c]
    exact (div_le_iff₀ (hvpos i)).2 (hbounds i).2
  have hmul : c * v i = w i := by
    dsimp [c]
    field_simp [ne_of_gt (hvpos i)]
  have hupdate : Function.update u i (c * u i) = w := by
    funext j
    by_cases hji : j = i
    · subst j
      simp only [Function.update_self]
      rw [show u i = v i by simp [u], hmul]
    · simp [u, hji]
  have hscaled := theta_update_le u i c (by omega) hmhi hu_pos hc
  have hscaled' :
      Bandits.Support.ProductSetLaw.theta m w i ≤
        c * Bandits.Support.ProductSetLaw.theta m u i := by
    simpa only [hupdate] using hscaled
  have htheta_nonneg : 0 ≤ Bandits.Support.ProductSetLaw.theta m v i :=
    le_of_lt (Bandits.Support.ProductSetLaw.theta_pos v i (by omega) hmhi hvpos)
  have hc_nonneg : 0 ≤ c := le_trans (by norm_num) hc
  calc
    Bandits.Support.ProductSetLaw.theta m w i ≤
        c * Bandits.Support.ProductSetLaw.theta m u i := hscaled'
    _ ≤ c * Bandits.Support.ProductSetLaw.theta m v i :=
      mul_le_mul_of_nonneg_left hmonotone hc_nonneg
    _ ≤ 2 * Bandits.Support.ProductSetLaw.theta m v i :=
      mul_le_mul_of_nonneg_right hc2 htheta_nonneg

end Bandits.Support.ProductMarginalStability

end
