/-
Copyright (c) 2026 The Bandits Lean regret formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Powerset
public import Bandits.Support.FiniteNormalization
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Order
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

/-!
# Positive product-weight laws on fixed-size subsets

This module defines the product-weight law on the actual `m`-element subsets of
`Fin K` and proves its finite normalization and inclusion-marginal identities.
The definitions and formulas follow
`sources/zip4/manuscript/04_slow_fast_learner.tex:7-13`; the inclusion odds
application is discussed at lines 84-89, and the sum of the inclusion
marginals is used at lines 132-138. This is internal mathematical support; it
does not formalize the orientation rule, Newton's inequalities, or a
conditional stochastic process.
-/

public section

open scoped BigOperators

namespace Bandits.Support.ProductSetLaw

/-- The actual family of `m`-element subsets of the `K` arms. -/
@[expose] def support (K m : ℕ) : Finset (Finset (Fin K)) :=
  Finset.univ.powersetCard m

/-- A set in the support of the product-weight law. -/
abbrev ProductSet (K m : ℕ) := {S : Finset (Fin K) // S ∈ support K m}

/-- The product weight assigned to a finite set of arms. -/
@[expose] def setWeight {K : ℕ} (w : Fin K → ℝ) (S : Finset (Fin K)) : ℝ :=
  ∏ i ∈ S, w i

/-- The normalizer, computed by the checked finite-support normalization API. -/
@[expose] noncomputable def normalizer {K : ℕ} (m : ℕ) (w : Fin K → ℝ) : ℝ :=
  FiniteNormalization.totalMass (support K m) (setWeight w)

/-- The source product-weight atom on the subtype of supported `m`-sets. -/
@[expose] noncomputable def Q {K : ℕ} (m : ℕ) (w : Fin K → ℝ)
    (S : ProductSet K m) : ℝ :=
  FiniteNormalization.normalizedWeight (support K m) (setWeight w) S.1

/-- The inclusion marginal of arm `i`, summed over supported sets containing it. -/
@[expose] noncomputable def theta {K : ℕ} (m : ℕ) (w : Fin K → ℝ)
    (i : Fin K) : ℝ :=
  FiniteNormalization.mass (support K m) (setWeight w)
    ((support K m).filter fun S => i ∈ S)

private theorem support_filter_contains_eq_image {K m : ℕ} (i : Fin K)
    (hm : 0 < m) :
    (support K m).filter (fun S => i ∈ S) =
      ((Finset.univ.erase i).powersetCard (m - 1)).image (fun T => insert i T) := by
  have hsubset : ({i} : Finset (Fin K)) ⊆ Finset.univ := by simp
  have hcard : ({i} : Finset (Fin K)).card ≤ m := by simp; omega
  simpa [support, Finset.sdiff_singleton_eq_erase] using
    (Finset.filter_powersetCard_subset ({i} : Finset (Fin K)) Finset.univ m hsubset hcard)

private theorem support_filter_omits_eq_powerset {K m : ℕ} (i : Fin K) :
    (support K m).filter (fun S => i ∉ S) =
      (Finset.univ.erase i).powersetCard m := by
  classical
  ext S
  simp only [Finset.mem_filter, support, Finset.mem_powersetCard]
  constructor
  · rintro ⟨⟨_, hcard⟩, hnot⟩
    exact ⟨Finset.subset_erase.mpr ⟨by simp, hnot⟩, hcard⟩
  · rintro ⟨hsub, hcard⟩
    exact ⟨⟨(Finset.subset_erase.mp hsub).1, hcard⟩,
      (Finset.subset_erase.mp hsub).2⟩

/-- The support is nonempty when `0 < m < K`. -/
theorem support_nonempty {K m : ℕ} (_hm : 0 < m) (hmK : m < K) :
    (support K m).Nonempty := by
  rw [support, Finset.powersetCard_nonempty]
  simp
  omega

/-- Every product weight is positive when every arm weight is positive. -/
theorem setWeight_pos {K : ℕ} (w : Fin K → ℝ) (hw : ∀ i, 0 < w i)
    (S : Finset (Fin K)) : 0 < setWeight w S := by
  exact Finset.prod_pos fun i _ => hw i

/-- The normalizer is positive under the source cardinality and weight hypotheses. -/
theorem normalizer_pos {K m : ℕ} (w : Fin K → ℝ) (hm : 0 < m) (hmK : m < K)
    (hw : ∀ i, 0 < w i) : 0 < normalizer m w := by
  unfold normalizer
  apply FiniteNormalization.totalMass_pos
  · exact support_nonempty hm hmK
  · intro S hS
    exact setWeight_pos w hw S

/-- Every atom on the support subtype is positive. -/
theorem Q_pos {K m : ℕ} (w : Fin K → ℝ) (hm : 0 < m) (hmK : m < K)
    (hw : ∀ i, 0 < w i) (S : ProductSet K m) : 0 < Q m w S := by
  unfold Q
  exact div_pos (setWeight_pos w hw S.1) (normalizer_pos w hm hmK hw)

/-- The raw sum defining the normalizer is exactly the sum over `univ.powersetCard m`. -/
theorem normalizer_eq_support_sum {K m : ℕ} (w : Fin K → ℝ) :
    normalizer m w = ∑ S ∈ support K m, setWeight w S := rfl

/-- The normalized atoms on the actual powerset-card support sum to one. -/
theorem total_mass_eq_one {K m : ℕ} (w : Fin K → ℝ) (hm : 0 < m) (hmK : m < K)
    (hw : ∀ i, 0 < w i) :
    (∑ S ∈ support K m,
      FiniteNormalization.normalizedWeight (support K m) (setWeight w) S) = 1 := by
  apply FiniteNormalization.sum_normalizedWeight_eq_one
  · exact support_nonempty hm hmK
  · intro S hS
    exact setWeight_pos w hw S

/-- The atoms `Q` sum to one on their support subtype. -/
theorem Q_sum_eq_one {K m : ℕ} (w : Fin K → ℝ) (hm : 0 < m) (hmK : m < K)
    (hw : ∀ i, 0 < w i) :
    (∑ S : ProductSet K m, Q m w S) = 1 := by
  calc
    (∑ S : ProductSet K m, Q m w S) =
        ∑ S : ProductSet K m,
          FiniteNormalization.normalizedWeight (support K m) (setWeight w) S.1 := by
      apply Finset.sum_congr rfl
      intro S hS
      rfl
    _ = ∑ S ∈ support K m,
          FiniteNormalization.normalizedWeight (support K m) (setWeight w) S := by
      symm
      exact Finset.sum_subtype (support K m) (by intro S; rfl)
        (FiniteNormalization.normalizedWeight (support K m) (setWeight w))
    _ = 1 := total_mass_eq_one w hm hmK hw

private theorem setWeight_insert {K : ℕ} (w : Fin K → ℝ) (i : Fin K)
    (T : Finset (Fin K)) (hi : i ∉ T) :
    setWeight w (insert i T) = w i * setWeight w T := by
  simp [setWeight, hi]

private theorem containing_weight_sum {K m : ℕ} (w : Fin K → ℝ) (i : Fin K)
    (hm : 0 < m) :
    (∑ S ∈ support K m, if i ∈ S then setWeight w S else 0) =
      w i * (∑ T ∈ (Finset.univ.erase i).powersetCard (m - 1), setWeight w T) := by
  classical
  have hfilter := support_filter_contains_eq_image i hm
  have hinj : Set.InjOn (fun T : Finset (Fin K) => insert i T)
      ((Finset.univ.erase i).powersetCard (m - 1)) := by
    intro A hA B hB hAB
    have hA_not : i ∉ A := by
      intro hi
      have : i ∈ Finset.univ.erase i := (Finset.mem_powersetCard.mp hA).1 hi
      simp at this
    have hB_not : i ∉ B := by
      intro hi
      have : i ∈ Finset.univ.erase i := (Finset.mem_powersetCard.mp hB).1 hi
      simp at this
    have herase := congrArg (fun S : Finset (Fin K) => S.erase i) hAB
    simpa [hA_not, hB_not] using herase
  calc
    (∑ S ∈ support K m, if i ∈ S then setWeight w S else 0) =
        ∑ S ∈ (support K m).filter (fun S => i ∈ S), setWeight w S := by
      rw [← Finset.sum_filter]
    _ = ∑ T ∈ (Finset.univ.erase i).powersetCard (m - 1),
          setWeight w (insert i T) := by
      rw [hfilter, Finset.sum_image hinj]
    _ = w i * (∑ T ∈ (Finset.univ.erase i).powersetCard (m - 1), setWeight w T) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro T hT
      apply setWeight_insert
      intro hi
      have hmem : i ∈ Finset.univ.erase i :=
        (Finset.mem_powersetCard.mp hT).1 hi
      simp at hmem

/-- The inclusion marginal has the source's degree-`m-1` numerator. -/
theorem theta_eq_weight_mul_erased_sum_div {K m : ℕ} (w : Fin K → ℝ) (i : Fin K)
    (hm : 0 < m) :
    theta m w i =
      w i * (∑ T ∈ (Finset.univ.erase i).powersetCard (m - 1), setWeight w T) /
        normalizer m w := by
  calc
    theta m w i =
        (∑ S ∈ (support K m).filter (fun S => i ∈ S), setWeight w S) /
          normalizer m w := by
      unfold theta FiniteNormalization.mass FiniteNormalization.normalizedWeight normalizer
      rw [← Finset.sum_div, Finset.sum_filter]
    _ =
        w i * (∑ T ∈ (Finset.univ.erase i).powersetCard (m - 1), setWeight w T) /
          normalizer m w := by
      rw [Finset.sum_filter, containing_weight_sum w i hm]

private theorem omitting_weight_sum {K m : ℕ} (w : Fin K → ℝ) (i : Fin K) :
    (∑ S ∈ support K m, if i ∉ S then setWeight w S else 0) =
      ∑ T ∈ (Finset.univ.erase i).powersetCard m, setWeight w T := by
  rw [← Finset.sum_filter, support_filter_omits_eq_powerset]

private theorem omitted_mass_eq_erased_sum_div {K m : ℕ} (w : Fin K → ℝ)
    (i : Fin K) :
    FiniteNormalization.mass (support K m) (setWeight w)
      ((support K m).filter fun S => i ∉ S) =
      (∑ T ∈ (Finset.univ.erase i).powersetCard m, setWeight w T) /
        normalizer m w := by
  unfold FiniteNormalization.mass FiniteNormalization.normalizedWeight normalizer
  rw [← Finset.sum_div]
  rw [Finset.sum_filter, omitting_weight_sum]

/-- The complement marginal has the source's degree-`m` numerator. -/
theorem one_sub_theta_eq_erased_sum_div {K m : ℕ} (w : Fin K → ℝ) (i : Fin K)
    (hm : 0 < m) (hmK : m < K) (hw : ∀ j, 0 < w j) :
    1 - theta m w i =
      (∑ T ∈ (Finset.univ.erase i).powersetCard m, setWeight w T) /
        normalizer m w := by
  have htotal := total_mass_eq_one w hm hmK hw
  have hsplit : theta m w i +
      FiniteNormalization.mass (support K m) (setWeight w)
        ((support K m).filter fun S => i ∉ S) = 1 := by
    calc
      _ = (∑ S ∈ (support K m).filter (fun S => i ∈ S),
            FiniteNormalization.normalizedWeight (support K m) (setWeight w) S) +
          (∑ S ∈ (support K m).filter (fun S => i ∉ S),
            FiniteNormalization.normalizedWeight (support K m) (setWeight w) S) := by
        rfl
      _ = ∑ S ∈ support K m,
            FiniteNormalization.normalizedWeight (support K m) (setWeight w) S := by
        rw [Finset.sum_filter_add_sum_filter_not]
      _ = 1 := htotal
  rw [omitted_mass_eq_erased_sum_div w i] at hsplit
  linarith

private theorem support_filter_contains_nonempty {K m : ℕ} (i : Fin K)
    (hm : 0 < m) (hmK : m < K) :
    ((support K m).filter fun S => i ∈ S).Nonempty := by
  rw [support_filter_contains_eq_image i hm]
  have hi : i ∈ (Finset.univ : Finset (Fin K)) := Finset.mem_univ i
  have hcard : (Finset.univ.erase i).card = K - 1 := by
    rw [Finset.card_erase_of_mem hi]
    simp
  have hle : m - 1 ≤ (Finset.univ.erase i).card := by omega
  obtain ⟨T, hT⟩ := Finset.powersetCard_nonempty.mpr hle
  exact ⟨insert i T, Finset.mem_image.mpr ⟨T, hT, rfl⟩⟩

private theorem support_filter_omits_nonempty {K m : ℕ} (i : Fin K)
    (hmK : m < K) :
    ((support K m).filter fun S => i ∉ S).Nonempty := by
  rw [support_filter_omits_eq_powerset]
  have hi : i ∈ (Finset.univ : Finset (Fin K)) := Finset.mem_univ i
  have hcard : (Finset.univ.erase i).card = K - 1 := by
    rw [Finset.card_erase_of_mem hi]
    simp
  have hle : m ≤ (Finset.univ.erase i).card := by omega
  exact Finset.powersetCard_nonempty.mpr hle

/-- Every arm has strictly positive inclusion probability. -/
theorem theta_pos {K m : ℕ} (w : Fin K → ℝ) (i : Fin K)
    (hm : 0 < m) (hmK : m < K) (hw : ∀ j, 0 < w j) : 0 < theta m w i := by
  apply FiniteNormalization.mass_pos
  · exact Finset.filter_subset _ _
  · exact support_filter_contains_nonempty i hm hmK
  · intro S hS
    exact setWeight_pos w hw S

/-- Every arm has strictly positive exclusion probability. -/
theorem one_sub_theta_pos {K m : ℕ} (w : Fin K → ℝ) (i : Fin K)
    (hm : 0 < m) (hmK : m < K) (hw : ∀ j, 0 < w j) :
    0 < 1 - theta m w i := by
  rw [one_sub_theta_eq_erased_sum_div w i hm hmK hw]
  have hcard : ((Finset.univ.erase i).powersetCard m).Nonempty := by
    rw [← support_filter_omits_eq_powerset i]
    exact support_filter_omits_nonempty i hmK
  have hsum : 0 <
      ∑ T ∈ (Finset.univ.erase i).powersetCard m, setWeight w T := by
    apply Finset.sum_pos
    · intro T hT
      exact setWeight_pos w hw T
    · exact hcard
  exact div_pos hsum (normalizer_pos w hm hmK hw)

/-- Each inclusion marginal is strictly less than one. -/
theorem theta_lt_one {K m : ℕ} (w : Fin K → ℝ) (i : Fin K)
    (hm : 0 < m) (hmK : m < K) (hw : ∀ j, 0 < w j) : theta m w i < 1 := by
  have h := one_sub_theta_pos w i hm hmK hw
  linarith

/-- The sum of all inclusion marginals is `m`, by double-counting each supported set. -/
theorem sum_theta_eq_card {K m : ℕ} (w : Fin K → ℝ) (hm : 0 < m)
    (hmK : m < K) (hw : ∀ j, 0 < w j) :
    (∑ i : Fin K, theta m w i) = (m : ℝ) := by
  classical
  let q : Finset (Fin K) → ℝ :=
    FiniteNormalization.normalizedWeight (support K m) (setWeight w)
  have htheta (i : Fin K) : theta m w i =
      ∑ S ∈ support K m, if i ∈ S then q S else 0 := by
    simp [theta, q, FiniteNormalization.mass, Finset.sum_filter]
  have hinner (S : Finset (Fin K)) (hS : S ∈ support K m) :
      (∑ i : Fin K, if i ∈ S then q S else 0) = (m : ℝ) * q S := by
    have hfilter : (Finset.univ : Finset (Fin K)).filter (fun i => i ∈ S) = S := by
      ext i
      simp
    rw [← Finset.sum_filter, hfilter, Finset.sum_const]
    have hcard : S.card = m := (Finset.mem_powersetCard.mp hS).2
    simp [hcard]
  calc
    (∑ i : Fin K, theta m w i) =
        ∑ i ∈ (Finset.univ : Finset (Fin K)), ∑ S ∈ support K m,
          if i ∈ S then q S else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      exact htheta i
    _ = ∑ S ∈ support K m, ∑ i : Fin K, if i ∈ S then q S else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ S ∈ support K m, (m : ℝ) * q S := by
      apply Finset.sum_congr rfl
      intro S hS
      exact hinner S hS
    _ = (m : ℝ) * ∑ S ∈ support K m, q S := by
      rw [← Finset.mul_sum]
    _ = (m : ℝ) := by
      dsimp [q]
      have hnorm :
          (∑ S ∈ support K m,
            FiniteNormalization.normalizedWeight (support K m) (setWeight w) S) = 1 :=
        total_mass_eq_one w hm hmK hw
      rw [hnorm]
      ring

end Bandits.Support.ProductSetLaw
