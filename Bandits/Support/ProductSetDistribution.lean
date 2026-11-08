/-
Copyright (c) 2026 The Bandits Lean regret formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ProductSetLaw
public import Bandits.Support.PositiveWeightPMF
public import Bandits.Support.ElementarySymmetricRecurrence
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# PMF API for the product-weight fixed-size set law

This module puts the accepted arithmetic law from
`sources/zip4/manuscript/04_slow_fast_learner.tex:7-13` on its actual
`powersetCard` subtype. It connects the existing `Q` and `theta` formulas to
the PMF, elementary symmetric sums, and the inclusion odds in lines 84-89.
It does not formalize the prefix sampler or the monotonicity of the marginal.

## Main results

- `productSetPMF`: the positive-weight PMF on `ProductSetLaw.ProductSet`.
- `productSetPMF_apply_eq_Q` and `productSetPMF_event_eq_theta`: its point and
  inclusion-event probabilities.
- The normalizer and erased-coordinate numerator identities with elementary
  symmetric sums.
- `theta_odds_eq_erased_elementarySymmetric`: the source inclusion-odds formula.
-/

public section

open scoped BigOperators

namespace Bandits.Support.ProductSetDistribution

open Bandits.Support

/-- The probability law on the actual supported `m`-subsets of `Fin K`.

The source validity data `0 < m < K` and strict positivity of every arm weight
are arguments of the definition. Nonemptiness of the powerset-card support and
positivity of its product weights are derived from that data.

Source: `sources/zip4/manuscript/04_slow_fast_learner.tex:7-13`. -/
@[expose] noncomputable def productSetPMF {K m : ℕ} (w : Fin K → ℝ)
    (hm : 0 < m) (hmK : m < K) (hw : ∀ i, 0 < w i) :
    PMF (ProductSetLaw.ProductSet K m) :=
  PositiveWeightPMF.ofPositiveWeights (ProductSetLaw.support K m)
    (ProductSetLaw.setWeight w)
    (ProductSetLaw.support_nonempty hm hmK)
    (fun S _ => ProductSetLaw.setWeight_pos w hw S)

/-- A supported set has the source product-weight mass `ENNReal.ofReal Q`. -/
theorem productSetPMF_apply_eq_Q {K m : ℕ} (w : Fin K → ℝ)
    (hm : 0 < m) (hmK : m < K) (hw : ∀ i, 0 < w i)
    (S : ProductSetLaw.ProductSet K m) :
    productSetPMF w hm hmK hw S = ENNReal.ofReal (ProductSetLaw.Q m w S) := by
  rw [productSetPMF, PositiveWeightPMF.ofPositiveWeights_apply]
  rfl

/-- Taking `toReal` of a point mass recovers the canonical arithmetic `Q`. -/
theorem productSetPMF_toReal_apply_eq_Q {K m : ℕ} (w : Fin K → ℝ)
    (hm : 0 < m) (hmK : m < K) (hw : ∀ i, 0 < w i)
    (S : ProductSetLaw.ProductSet K m) :
    (productSetPMF w hm hmK hw S).toReal = ProductSetLaw.Q m w S := by
  rw [productSetPMF_apply_eq_Q]
  exact ENNReal.toReal_ofReal (ProductSetLaw.Q_pos w hm hmK hw S).le

/-- The canonical inclusion marginal is the finite sum of `Q` over the
supported sets containing the arm. -/
theorem theta_eq_sum_productSet_Q {K m : ℕ} (w : Fin K → ℝ) (i : Fin K) :
    ProductSetLaw.theta m w i =
      ∑ S : ProductSetLaw.ProductSet K m,
        if i ∈ S.1 then ProductSetLaw.Q m w S else 0 := by
  classical
  calc
    ProductSetLaw.theta m w i =
        ∑ S ∈ (ProductSetLaw.support K m).filter (fun S => i ∈ S),
          FiniteNormalization.normalizedWeight (ProductSetLaw.support K m)
            (ProductSetLaw.setWeight w) S := rfl
    _ = ∑ S ∈ ProductSetLaw.support K m,
          if i ∈ S then
            FiniteNormalization.normalizedWeight (ProductSetLaw.support K m)
              (ProductSetLaw.setWeight w) S else 0 := by
      rw [← Finset.sum_filter]
    _ = ∑ S : ProductSetLaw.ProductSet K m,
          if i ∈ S.1 then ProductSetLaw.Q m w S else 0 := by
      symm
      simpa only [ProductSetLaw.Q] using
        (Finset.sum_subtype (ProductSetLaw.support K m) (by intro S; rfl)
          (fun S => if i ∈ S then
            FiniteNormalization.normalizedWeight (ProductSetLaw.support K m)
              (ProductSetLaw.setWeight w) S else 0)).symm

/-- The PMF probability of including arm `i`, expressed as a finite sum on its
actual subtype carrier, is exactly the canonical `theta`. -/
theorem productSetPMF_event_eq_theta {K m : ℕ} (w : Fin K → ℝ) (i : Fin K)
    (hm : 0 < m) (hmK : m < K) (hw : ∀ j, 0 < w j) :
    (∑ S : ProductSetLaw.ProductSet K m,
      if i ∈ S.1 then productSetPMF w hm hmK hw S else 0) =
      ENNReal.ofReal (ProductSetLaw.theta m w i) := by
  classical
  calc
    _ = ENNReal.ofReal
        (∑ S : ProductSetLaw.ProductSet K m,
          if i ∈ S.1 then ProductSetLaw.Q m w S else 0) := by
      rw [ENNReal.ofReal_sum_of_nonneg (s := Finset.univ)]
      · apply Finset.sum_congr rfl
        intro S hS
        split_ifs with hi
        · rw [productSetPMF_apply_eq_Q]
        · simp
      · intro S hS
        split_ifs
        · exact (ProductSetLaw.Q_pos w hm hmK hw S).le
        · exact le_rfl
    _ = ENNReal.ofReal (ProductSetLaw.theta m w i) := by
      rw [← theta_eq_sum_productSet_Q]

/-- The source normalizer is the degree-`m` elementary symmetric sum. -/
theorem normalizer_eq_elementarySymmetric {K m : ℕ} (w : Fin K → ℝ) :
    ProductSetLaw.normalizer m w =
      ElementarySymmetricRecurrence.elementarySymmetric w Finset.univ m := by
  rw [ProductSetLaw.normalizer_eq_support_sum]
  rfl

/-- The same normalizer is the multiset elementary symmetric sum. -/
theorem normalizer_eq_multiset_esymm {K m : ℕ} (w : Fin K → ℝ) :
    ProductSetLaw.normalizer m w = (Finset.univ.val.map w).esymm m := by
  rw [normalizer_eq_elementarySymmetric]
  exact ElementarySymmetricRecurrence.elementarySymmetric_eq_multiset_esymm
    w Finset.univ m

/-- The inclusion numerator is the degree-`m-1` elementary symmetric sum after
deleting coordinate `i`. -/
theorem inclusionNumerator_eq_elementarySymmetric {K m : ℕ} (w : Fin K → ℝ)
    (i : Fin K) :
    (∑ T ∈ (Finset.univ.erase i).powersetCard (m - 1),
      ProductSetLaw.setWeight w T) =
      ElementarySymmetricRecurrence.elementarySymmetric w
        (Finset.univ.erase i) (m - 1) := rfl

/-- The exclusion numerator is the degree-`m` elementary symmetric sum after
deleting coordinate `i`. -/
theorem exclusionNumerator_eq_elementarySymmetric {K m : ℕ} (w : Fin K → ℝ)
    (i : Fin K) :
    (∑ T ∈ (Finset.univ.erase i).powersetCard m, ProductSetLaw.setWeight w T) =
      ElementarySymmetricRecurrence.elementarySymmetric w
        (Finset.univ.erase i) m := rfl

/-- The inclusion marginal in elementary-symmetric form. -/
theorem theta_eq_inclusionNumerator_div_normalizer {K m : ℕ}
    (w : Fin K → ℝ) (i : Fin K) (hm : 0 < m) :
    ProductSetLaw.theta m w i =
      w i * ElementarySymmetricRecurrence.elementarySymmetric w
        (Finset.univ.erase i) (m - 1) / ProductSetLaw.normalizer m w := by
  rw [ProductSetLaw.theta_eq_weight_mul_erased_sum_div w i hm,
    inclusionNumerator_eq_elementarySymmetric]

/-- The exclusion marginal in elementary-symmetric form. -/
theorem one_sub_theta_eq_exclusionNumerator_div_normalizer {K m : ℕ}
    (w : Fin K → ℝ) (i : Fin K) (hm : 0 < m) (hmK : m < K)
    (hw : ∀ j, 0 < w j) :
    1 - ProductSetLaw.theta m w i =
      ElementarySymmetricRecurrence.elementarySymmetric w
        (Finset.univ.erase i) m / ProductSetLaw.normalizer m w := by
  rw [ProductSetLaw.one_sub_theta_eq_erased_sum_div w i hm hmK hw,
    exclusionNumerator_eq_elementarySymmetric]

private theorem erased_card {K : ℕ} (i : Fin K) :
    (Finset.univ.erase i).card = K - 1 := by
  have hi : i ∈ (Finset.univ : Finset (Fin K)) := Finset.mem_univ i
  rw [Finset.card_erase_of_mem hi]
  simp

/-- Both erased-coordinate symmetric sums used in the odds formula are
strictly positive, with their degree bounds derived from `0 < m < K`. -/
theorem erased_numerators_pos {K m : ℕ} (w : Fin K → ℝ) (i : Fin K)
    (hm : 0 < m) (hmK : m < K) (hw : ∀ j, 0 < w j) :
    0 < ElementarySymmetricRecurrence.elementarySymmetric w
        (Finset.univ.erase i) (m - 1) ∧
    0 < ElementarySymmetricRecurrence.elementarySymmetric w
        (Finset.univ.erase i) m := by
  have hcard := erased_card i
  have hw' : ∀ j ∈ Finset.univ.erase i, 0 < w j := by
    intro j hj
    exact hw j
  constructor
  · apply ElementarySymmetricRecurrence.elementarySymmetric_pos
    · exact hw'
    · omega
  · apply ElementarySymmetricRecurrence.elementarySymmetric_pos
    · exact hw'
    · omega

/-- The source inclusion-odds identity. Positivity of the erased degree-`m`
sum justifies its denominator; all degree bounds follow from `0 < m < K`.

Source: `sources/zip4/manuscript/04_slow_fast_learner.tex:84-89`. -/
theorem theta_odds_eq_erased_elementarySymmetric {K m : ℕ} (w : Fin K → ℝ)
    (i : Fin K) (hm : 0 < m) (hmK : m < K) (hw : ∀ j, 0 < w j) :
    ProductSetLaw.theta m w i / (1 - ProductSetLaw.theta m w i) =
      w i * ElementarySymmetricRecurrence.elementarySymmetric w
        (Finset.univ.erase i) (m - 1) /
        ElementarySymmetricRecurrence.elementarySymmetric w
          (Finset.univ.erase i) m := by
  have hnormalizer : 0 < ProductSetLaw.normalizer m w :=
    ProductSetLaw.normalizer_pos w hm hmK hw
  have hnumerators := erased_numerators_pos w i hm hmK hw
  have hdenominator : 0 < 1 - ProductSetLaw.theta m w i :=
    ProductSetLaw.one_sub_theta_pos w i hm hmK hw
  have hratioDenominator :
      0 < ElementarySymmetricRecurrence.elementarySymmetric w
          (Finset.univ.erase i) m / ProductSetLaw.normalizer m w := by
    rw [← one_sub_theta_eq_exclusionNumerator_div_normalizer w i hm hmK hw]
    exact hdenominator
  rw [one_sub_theta_eq_exclusionNumerator_div_normalizer w i hm hmK hw,
    theta_eq_inclusionNumerator_div_normalizer w i hm]
  field_simp [ne_of_gt hnormalizer, ne_of_gt hnumerators.2,
    ne_of_gt hratioDenominator]

end Bandits.Support.ProductSetDistribution

end
