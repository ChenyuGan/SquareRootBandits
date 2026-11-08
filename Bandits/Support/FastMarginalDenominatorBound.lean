/-
Copyright (c) 2026 The Bandits Lean regret formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ElementarySymmetricRecurrence
public import Bandits.Support.ProductSetLaw
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The finite denominator estimate for the fast marginal

Internal mathematics for `sources/zip4/manuscript/04_slow_fast_learner.tex:49-82`,
using the elementary sums and product law of lines 7-13. We prove the complement
comparison for every subset of the required size, so no largest-coordinate set
or matching is an input. The conditional orientation law is not used or defined
here; applying the final denominator estimate to that law remains separate.
-/

public section

open scoped BigOperators

namespace Bandits.Support.FastMarginalDenominatorBound

open Bandits.Support.ElementarySymmetricRecurrence

/-- The double count in manuscript lines 55-61: each degree-`m` product is
counted once for each of its `m` coordinates. No positivity is needed. -/
theorem elementarySymmetric_mul_degree_eq_sum_complement {α : Type*}
    [DecidableEq α] (v : α → ℝ) (J : Finset α) (m : ℕ) (hm : 0 < m) :
    (m : ℝ) * elementarySymmetric v J m =
      ∑ V ∈ J.powersetCard (m - 1), (∏ j ∈ V, v j) * ∑ j ∈ J \ V, v j := by
  classical
  have hcount :
      (∑ V ∈ J.powersetCard (m - 1), ∑ j ∈ J \ V, (∏ a ∈ V, v a) * v j) =
        ∑ T ∈ J.powersetCard m, ∑ _j ∈ T, ∏ a ∈ T, v a := by
    rw [Finset.sum_sigma', Finset.sum_sigma']
    apply Finset.sum_bij (fun p _ => ⟨insert p.2 p.1, p.2⟩)
    · intro p hp
      obtain ⟨hV, hj⟩ := Finset.mem_sigma.mp hp
      obtain ⟨hVJ, hVc⟩ := Finset.mem_powersetCard.mp hV
      obtain ⟨hjJ, hjV⟩ := Finset.mem_sdiff.mp hj
      apply Finset.mem_sigma.mpr
      refine ⟨Finset.mem_powersetCard.mpr ⟨Finset.insert_subset hjJ hVJ, ?_⟩,
        Finset.mem_insert_self _ _⟩
      rw [Finset.card_insert_of_notMem hjV, hVc]
      omega
    · intro p hp q hq hpq
      have hsets : insert p.2 p.1 = insert q.2 q.1 := congrArg Sigma.fst hpq
      have hcoords : p.2 = q.2 := congrArg Sigma.snd hpq
      have hpnot := (Finset.mem_sdiff.mp (Finset.mem_sigma.mp hp).2).2
      have hqnot := (Finset.mem_sdiff.mp (Finset.mem_sigma.mp hq).2).2
      have herase := congrArg (fun T : Finset α => T.erase p.2) hsets
      have hfirst : p.1 = q.1 := by
        rw [Finset.erase_insert hpnot, hcoords, Finset.erase_insert hqnot] at herase
        exact herase
      exact Sigma.ext hfirst (by simpa using hcoords)
    · intro p hp
      obtain ⟨hT, hjT⟩ := Finset.mem_sigma.mp hp
      obtain ⟨hTJ, hTc⟩ := Finset.mem_powersetCard.mp hT
      refine ⟨⟨p.1.erase p.2, p.2⟩, ?_, ?_⟩
      · apply Finset.mem_sigma.mpr
        refine ⟨Finset.mem_powersetCard.mpr ⟨(Finset.erase_subset _ _).trans hTJ, ?_⟩,
          Finset.mem_sdiff.mpr ⟨hTJ hjT, Finset.notMem_erase _ _⟩⟩
        rw [Finset.card_erase_of_mem hjT, hTc]
      · simp only [Finset.insert_erase hjT]
    · intro p hp
      have hjV := (Finset.mem_sdiff.mp (Finset.mem_sigma.mp hp).2).2
      rw [Finset.prod_insert hjV, mul_comm]
  calc
    (m : ℝ) * elementarySymmetric v J m =
        ∑ T ∈ J.powersetCard m, (m : ℝ) * ∏ a ∈ T, v a := by
      rw [elementarySymmetric, Finset.mul_sum]
    _ = ∑ T ∈ J.powersetCard m, ∑ _j ∈ T, ∏ a ∈ T, v a := by
      apply Finset.sum_congr rfl
      intro T hT
      simp only [Finset.sum_const, nsmul_eq_mul, (Finset.mem_powersetCard.mp hT).2]
    _ = ∑ V ∈ J.powersetCard (m - 1),
        (∏ j ∈ V, v j) * ∑ j ∈ J \ V, v j := by
      rw [← hcount]
      apply Finset.sum_congr rfl
      intro V _
      rw [Finset.mul_sum]

/-- A nonempty finite set of positive coordinates has positive inverse sum. -/
theorem inverse_sum_pos {α : Type*} (v : α → ℝ) (U : Finset α)
    (hv : ∀ a, 0 < v a) (hU : U.Nonempty) :
    0 < ∑ a ∈ U, (v a)⁻¹ := by
  exact Finset.sum_pos (fun a _ => inv_pos.mpr (hv a)) hU

private theorem fraction_nonneg (s x : ℝ) (hs : 0 < s) (hx : 0 < x) :
    0 ≤ x / (1 + s * x) := by positivity

private theorem fraction_le_self (s x : ℝ) (hs : 0 < s) (hx : 0 < x) :
    x / (1 + s * x) ≤ x := by
  apply (div_le_iff₀ (by positivity : 0 < 1 + s * x)).mpr
  nlinarith only [mul_pos hs hx, hx]

private theorem fraction_le_inverse (s x : ℝ) (hs : 0 < s) (hx : 0 < x) :
    x / (1 + s * x) ≤ s⁻¹ := by
  apply (div_le_iff₀ (by positivity : 0 < 1 + s * x)).mpr
  have hcancel : s⁻¹ * (s * x) = x := by rw [← mul_assoc, inv_mul_cancel₀ hs.ne', one_mul]
  rw [mul_add, mul_one, hcancel]
  exact le_add_of_nonneg_left (inv_nonneg.mpr hs.le)

/-- Manuscript lines 64-72, strengthened to every `V` of the same cardinality
as `U`. The equal difference cardinalities replace an explicit pairing. -/
theorem sum_fraction_le_complement {α : Type*} [DecidableEq α]
    (v : α → ℝ) (J U V : Finset α) (hv : ∀ a, 0 < v a)
    (hUJ : U ⊆ J) (hVJ : V ⊆ J) (hcard : U.card = V.card) (hU : U.Nonempty) :
    (∑ j ∈ J \ U, v j / (1 + (∑ a ∈ U, (v a)⁻¹) * v j)) ≤
      ∑ j ∈ J \ V, v j := by
  classical
  let s := ∑ a ∈ U, (v a)⁻¹
  have hs : 0 < s := inverse_sum_pos v U hv hU
  have hinv (a : α) (ha : a ∈ U) : s⁻¹ ≤ v a := by
    have hsingle : (v a)⁻¹ ≤ s :=
      Finset.single_le_sum (fun b _ => (inv_pos.mpr (hv b)).le) ha
    have hmul : 1 ≤ s * v a := (inv_le_iff_one_le_mul₀ (hv a)).mp hsingle
    exact (inv_le_iff_one_le_mul₀ hs).mpr (by simpa [mul_comm] using hmul)
  have hdiff : (V \ U).card = (U \ V).card :=
    Finset.card_sdiff_comm hcard.symm
  have hpaired : (∑ j ∈ V \ U, v j / (1 + s * v j)) ≤ ∑ a ∈ U \ V, v a := by
    calc
      _ ≤ ∑ _j ∈ V \ U, s⁻¹ :=
        Finset.sum_le_sum (fun j _ => fraction_le_inverse s (v j) hs (hv j))
      _ = ∑ _a ∈ U \ V, s⁻¹ := by simp only [Finset.sum_const, hdiff]
      _ ≤ _ := Finset.sum_le_sum (fun a ha => hinv a (Finset.mem_sdiff.mp ha).1)
  have hleft : J \ U = (V \ U) ∪ ((J \ U) \ V) := by
    ext a
    simp only [Finset.mem_sdiff, Finset.mem_union]
    constructor
    · rintro ⟨haJ, haU⟩
      by_cases haV : a ∈ V
      · exact Or.inl ⟨haV, haU⟩
      · exact Or.inr ⟨⟨haJ, haU⟩, haV⟩
    · rintro (⟨haV, haU⟩ | ⟨ha, _⟩)
      · exact ⟨hVJ haV, haU⟩
      · exact ha
  have hright : J \ V = (U \ V) ∪ ((J \ U) \ V) := by
    ext a
    simp only [Finset.mem_sdiff, Finset.mem_union]
    constructor
    · rintro ⟨haJ, haV⟩
      by_cases haU : a ∈ U
      · exact Or.inl ⟨haU, haV⟩
      · exact Or.inr ⟨⟨haJ, haU⟩, haV⟩
    · rintro (⟨haU, haV⟩ | ⟨⟨haJ, _⟩, haV⟩)
      · exact ⟨hUJ haU, haV⟩
      · exact ⟨haJ, haV⟩
  have hldisj : Disjoint (V \ U) ((J \ U) \ V) := by
    apply Finset.disjoint_left.mpr
    intro a ha hb
    exact (Finset.mem_sdiff.mp hb).2 (Finset.mem_sdiff.mp ha).1
  have hrdisj : Disjoint (U \ V) ((J \ U) \ V) := by
    apply Finset.disjoint_left.mpr
    intro a ha hb
    exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hb).1).2
      (Finset.mem_sdiff.mp ha).1
  change (∑ j ∈ J \ U, v j / (1 + s * v j)) ≤ _
  rw [hleft, Finset.sum_union hldisj, hright, Finset.sum_union hrdisj]
  exact add_le_add hpaired (Finset.sum_le_sum
    (fun j _ => fraction_le_self s (v j) hs (hv j)))

/-- Positivity of both erased elementary sums used in the denominator and odds
calculation (manuscript lines 50-79). -/
theorem erased_elementarySymmetric_pos {K m : ℕ} (v : Fin K → ℝ) (i : Fin K)
    (hm : 2 ≤ m) (hmK : m < K) (hv : ∀ j, 0 < v j) :
    0 < elementarySymmetric v (Finset.univ.erase i) (m - 1) ∧
      0 < elementarySymmetric v (Finset.univ.erase i) m := by
  have hJcard : (Finset.univ.erase i).card = K - 1 := by simp
  constructor
  · exact elementarySymmetric_pos v _ _ (fun j _ => hv j) (by omega)
  · exact elementarySymmetric_pos v _ _ (fun j _ => hv j) (by omega)

/-- The substantive finite estimates in manuscript lines 50-74. All inputs are
the actual positive weights, finite slow set, and source cardinality conditions.
In particular the weighted complement estimate is proved, not assumed. -/
theorem fast_remainder_bounds {K m : ℕ} (v : Fin K → ℝ)
    (U : Finset (Fin K)) (i : Fin K) (hm : 2 ≤ m) (hmK : m < K)
    (hv : ∀ j, 0 < v j) (hU : U.card = m - 1) (hi : i ∉ U) :
    let J := Finset.univ.erase i
    let s := ∑ a ∈ U, (v a)⁻¹
    let W := ∑ j ∈ Finset.univ \ insert i U, v j / (1 + s * v j)
    0 < s ∧ 0 ≤ W ∧ s * W ≤ (K - m : ℕ) ∧
      0 < elementarySymmetric v J (m - 1) ∧
      0 < elementarySymmetric v J m ∧
      W ≤ (m : ℝ) * elementarySymmetric v J m / elementarySymmetric v J (m - 1) := by
  classical
  let J := Finset.univ.erase i
  let s := ∑ a ∈ U, (v a)⁻¹
  let R := Finset.univ \ insert i U
  let W := ∑ j ∈ R, v j / (1 + s * v j)
  change 0 < s ∧ 0 ≤ W ∧ s * W ≤ (K - m : ℕ) ∧ _
  have hUne : U.Nonempty := Finset.card_pos.mp (by omega)
  have hs : 0 < s := inverse_sum_pos v U hv hUne
  have hWnonneg : 0 ≤ W :=
    Finset.sum_nonneg (fun j _ => fraction_nonneg s (v j) hs (hv j))
  have hUJ : U ⊆ J := by
    intro a ha
    exact Finset.mem_erase.mpr ⟨ne_of_mem_of_not_mem ha hi, Finset.mem_univ a⟩
  have hR : J \ U = R := by
    ext j
    simp only [J, R, Finset.mem_sdiff, Finset.mem_erase, Finset.mem_univ,
      Finset.mem_insert, and_true, true_and, not_or]
  have hRcard : R.card = K - m := by
    dsimp [R]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
      Fintype.card_fin, Finset.card_insert_of_notMem hi, hU]
    omega
  have hsW : s * W ≤ (K - m : ℕ) := by
    calc
      s * W = ∑ j ∈ R, s * (v j / (1 + s * v j)) := Finset.mul_sum R _ s
      _ ≤ ∑ _j ∈ R, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro j _
        have h := mul_le_mul_of_nonneg_left (fraction_le_inverse s (v j) hs (hv j)) hs.le
        simpa only [mul_inv_cancel₀ hs.ne'] using h
      _ = (K - m : ℕ) := by simp only [Finset.sum_const, nsmul_eq_mul, mul_one, hRcard]
  obtain ⟨hEprev, hE⟩ := erased_elementarySymmetric_pos v i hm hmK hv
  have hweighted : W * elementarySymmetric v J (m - 1) ≤
      (m : ℝ) * elementarySymmetric v J m := by
    calc
      W * elementarySymmetric v J (m - 1) =
          ∑ V ∈ J.powersetCard (m - 1), (∏ j ∈ V, v j) * W := by
        rw [elementarySymmetric, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro V _
        exact mul_comm _ _
      _ ≤ ∑ V ∈ J.powersetCard (m - 1), (∏ j ∈ V, v j) * ∑ j ∈ J \ V, v j := by
        apply Finset.sum_le_sum
        intro V hV
        obtain ⟨hVJ, hVc⟩ := Finset.mem_powersetCard.mp hV
        have hcomp : W ≤ ∑ j ∈ J \ V, v j := by
          dsimp [W]
          rw [← hR]
          exact sum_fraction_le_complement v J U V hv hUJ hVJ (hU.trans hVc.symm) hUne
        exact mul_le_mul_of_nonneg_left hcomp (Finset.prod_nonneg (fun j _ => (hv j).le))
      _ = (m : ℝ) * elementarySymmetric v J m :=
        (elementarySymmetric_mul_degree_eq_sum_complement v J m (by omega)).symm
  exact ⟨hs, hWnonneg, hsW, hEprev, hE, (le_div_iff₀ hEprev).mpr hweighted⟩

/-- The source ratio identity at line 74, derived from the canonical
`ProductSetLaw.theta` inclusion and complement formulas of lines 7-13. -/
theorem erased_elementarySymmetric_ratio_div_weight_eq_odds {K m : ℕ}
    (v : Fin K → ℝ) (i : Fin K) (hm : 2 ≤ m) (hmK : m < K)
    (hv : ∀ j, 0 < v j) :
    (elementarySymmetric v (Finset.univ.erase i) m /
        elementarySymmetric v (Finset.univ.erase i) (m - 1)) / v i =
      (1 - ProductSetLaw.theta m v i) / ProductSetLaw.theta m v i := by
  have hmpos : 0 < m := by omega
  have hinc := ProductSetLaw.theta_eq_weight_mul_erased_sum_div v i hmpos
  have hexc := ProductSetLaw.one_sub_theta_eq_erased_sum_div v i hmpos hmK hv
  change ProductSetLaw.theta m v i =
    v i * elementarySymmetric v (Finset.univ.erase i) (m - 1) /
      ProductSetLaw.normalizer m v at hinc
  change 1 - ProductSetLaw.theta m v i =
    elementarySymmetric v (Finset.univ.erase i) m / ProductSetLaw.normalizer m v at hexc
  have hEprev := (erased_elementarySymmetric_pos v i hm hmK hv).1
  have hZ := ProductSetLaw.normalizer_pos v hmpos hmK hv
  rw [hexc, hinc]
  field_simp [(hv i).ne', hEprev.ne', hZ.ne']

/-- The denominator estimate in manuscript lines 74-79, with the actual
canonical product-law inclusion marginal. Applying it to the reciprocal of the
conditional fast marginal requires the separately proved orientation equality. -/
theorem fast_marginal_denominator_bound {K m : ℕ} (v : Fin K → ℝ)
    (U : Finset (Fin K)) (i : Fin K) (hm : 2 ≤ m) (hmK : m < K)
    (hv : ∀ j, 0 < v j) (hU : U.card = m - 1) (hi : i ∉ U) :
    let s := ∑ a ∈ U, (v a)⁻¹
    let W := ∑ j ∈ Finset.univ \ insert i U, v j / (1 + s * v j)
    1 + W / v i + s * W ≤ (K - m + 1 : ℕ) +
      (m : ℝ) * (1 - ProductSetLaw.theta m v i) / ProductSetLaw.theta m v i := by
  classical
  let s := ∑ a ∈ U, (v a)⁻¹
  let W := ∑ j ∈ Finset.univ \ insert i U, v j / (1 + s * v j)
  change 1 + W / v i + s * W ≤ _
  obtain ⟨_, _, hsW, _, _, hW⟩ := fast_remainder_bounds v U i hm hmK hv hU hi
  have hWdiv : W / v i ≤
      (m : ℝ) * (1 - ProductSetLaw.theta m v i) / ProductSetLaw.theta m v i := by
    calc
      W / v i ≤ ((m : ℝ) * elementarySymmetric v (Finset.univ.erase i) m /
          elementarySymmetric v (Finset.univ.erase i) (m - 1)) / v i :=
        div_le_div_of_nonneg_right hW (hv i).le
      _ = (m : ℝ) * ((elementarySymmetric v (Finset.univ.erase i) m /
          elementarySymmetric v (Finset.univ.erase i) (m - 1)) / v i) := by ring
      _ = _ := by
        rw [erased_elementarySymmetric_ratio_div_weight_eq_odds v i hm hmK hv]
        ring
  simp only [Nat.cast_add, Nat.cast_one]
  linarith only [hsW, hWdiv]

end Bandits.Support.FastMarginalDenominatorBound
