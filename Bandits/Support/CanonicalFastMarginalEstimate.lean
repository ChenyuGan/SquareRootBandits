/-
Copyright (c) 2026 The Bandits Lean regret formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.FiniteOrientationDisintegration
public import Bandits.Support.ProductSetLaw
import Bandits.Support.FastMarginalDenominatorBound
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Canonical lower bound for the conditional fast marginal

This module applies the accepted finite denominator estimate to the actual
`FiniteOrientationDisintegration.conditionalFastLaw` on `Fin K`, with the
fixed inverse anchor `v` in both current-weight laws.

The source formulas are in
`sources/zip4/manuscript/04_slow_fast_learner.tex:24-46,49-82`. These are
fully proved internal marginal results; they do not close the joint learner
lemma or the recording and operational sampling laws.
-/

public section

open scoped BigOperators

namespace Bandits.Support.CanonicalFastMarginalEstimate

open Bandits.Support.FiniteOrientationDisintegration
open Bandits.Support.FastMarginalDenominatorBound
open Bandits.Support.ProductSetLaw

private theorem reciprocal_fraction_sum (x s W : ℝ) (hx : x ≠ 0)
    (hd : 1 + s * x ≠ 0) :
    1 / ((x / (1 + s * x)) / (x / (1 + s * x) + W)) =
      1 + W / x + s * W := by
  have hd' : 1 + x * s ≠ 0 := by simpa only [mul_comm] using hd
  field_simp [hx, hd, hd']
  ring

/-- The reciprocal of the existing conditional law with current weights and
anchor both equal to `v` is the source expression `1 + W / v i + s * W`.

Here `W` sums the accepted complement weights over
`univ \ insert i U`, with each term divided by its existing candidate
denominator. The set, support, and candidate proofs are constructed from the
cardinality and non-membership inputs.

Source: `sources/zip4/manuscript/04_slow_fast_learner.tex:24-29,49-74`. -/
theorem conditionalFastLaw_reciprocal_eq {K : ℕ} (v : Fin K → ℝ)
    (U : Finset (Fin K)) (i : Fin K) (hv : ∀ a, 0 < v a) (hi : i ∉ U) :
    let s := ∑ a ∈ U, (v a)⁻¹
    let W := ∑ j ∈ (Finset.univ : Finset (Fin K)) \ insert i U,
      v j / (1 + s * v j)
    1 / conditionalFastLaw (Finset.univ : Finset (Fin K)) v v U
      (Finset.subset_univ U) ⟨i, by simp [hi]⟩
      (fun a _ => hv a) (fun a _ => hv a) ⟨i, by simp [hi]⟩ =
      1 + W / v i + s * W := by
  classical
  let C : Finset (Fin K) := Finset.univ \ U
  let s : ℝ := ∑ a ∈ U, (v a)⁻¹
  let W : ℝ := ∑ j ∈ (Finset.univ : Finset (Fin K)) \ insert i U,
    v j / (1 + s * v j)
  have hiC : i ∈ C := by
    simp only [C, Finset.mem_sdiff, Finset.mem_univ, true_and]
    exact hi
  have hR : C.erase i =
      (Finset.univ : Finset (Fin K)) \ insert i U := by
    ext j
    simp only [C, Finset.mem_erase, Finset.mem_sdiff, Finset.mem_univ,
      Finset.mem_insert, true_and, not_or]
  have hs : s = inverseAnchorSum v U := by
    simp [s, inverseAnchorSum, one_div]
  have hnormalizer : candidateNormalizer (Finset.univ : Finset (Fin K)) v v U =
      v i / (1 + s * v i) + W := by
    calc
      candidateNormalizer (Finset.univ : Finset (Fin K)) v v U =
          ∑ j ∈ C.attach, v j / (1 + s * v j) := by
        unfold candidateNormalizer
        change (∑ j ∈ C.attach, candidateWeight v v U j.1) = _
        apply Finset.sum_congr rfl
        intro j hj
        rw [candidateWeight, ← hs]
      _ = v i / (1 + s * v i) + W := by
        rw [C.sum_attach (f := fun j => v j / (1 + s * v j)),
          ← C.sum_erase_add
          (fun j => v j / (1 + s * v j)) hiC, hR]
        change W + v i / (1 + s * v i) =
          v i / (1 + s * v i) + W
        exact add_comm _ _
  have hdenom : 0 < 1 + s * v i := by
    have hsNonneg := inverseAnchorSum_nonneg (Finset.univ : Finset (Fin K)) U v
      (Finset.subset_univ U) (fun a _ => hv a)
    have hs' : 0 ≤ s := by rw [hs]; exact hsNonneg
    exact add_pos_of_pos_of_nonneg zero_lt_one
      (mul_nonneg hs' (hv i).le)
  change 1 / (candidateWeight v v U i /
      candidateNormalizer (Finset.univ : Finset (Fin K)) v v U) = _
  rw [hnormalizer]
  rw [candidateWeight, ← hs]
  exact reciprocal_fraction_sum (v i) s W (ne_of_gt (hv i)) (ne_of_gt hdenom)

/-- The accepted finite denominator estimate implies the canonical conditional
fast marginal lower bound at fixed current weights and anchor `v`.

Source: `sources/zip4/manuscript/04_slow_fast_learner.tex:49-82`. -/
theorem conditionalFastLaw_lower_bound {K m : ℕ} (v : Fin K → ℝ)
    (U : Finset (Fin K)) (i : Fin K) (hm : 2 ≤ m) (hmK : m < K)
    (hv : ∀ a, 0 < v a) (hU : U.card = m - 1) (hi : i ∉ U) :
    conditionalFastLaw (Finset.univ : Finset (Fin K)) v v U
      (Finset.subset_univ U) ⟨i, by simp [hi]⟩
      (fun a _ => hv a) (fun a _ => hv a) ⟨i, by simp [hi]⟩ ≥
      theta m v i /
        (((K - m + 1 : ℕ) : ℝ) * theta m v i +
          (m : ℝ) * (1 - theta m v i)) := by
  classical
  let s : ℝ := ∑ a ∈ U, (v a)⁻¹
  let W : ℝ := ∑ j ∈ (Finset.univ : Finset (Fin K)) \ insert i U,
    v j / (1 + s * v j)
  let q : ℝ := conditionalFastLaw (Finset.univ : Finset (Fin K)) v v U
    (Finset.subset_univ U) ⟨i, by simp [hi]⟩
    (fun a _ => hv a) (fun a _ => hv a) ⟨i, by simp [hi]⟩
  have htheta : 0 < theta m v i := theta_pos v i (by omega) hmK hv
  have hthetaOne : theta m v i < 1 := theta_lt_one v i (by omega) hmK hv
  have hqpos := conditionalFastLaw_pos (Finset.univ : Finset (Fin K)) U v v
    (Finset.subset_univ U) ⟨i, by simp [hi]⟩
    (fun a _ => hv a) (fun a _ => hv a) ⟨i, by simp [hi]⟩
  have hqposReal : 0 < q := by
    simpa only [q] using hqpos
  have hrec := conditionalFastLaw_reciprocal_eq v U i hv hi
  have hrecBound := fast_marginal_denominator_bound v U i hm hmK hv hU hi
  change 1 + W / v i + s * W ≤
      ((K - m + 1 : ℕ) : ℝ) +
        (m : ℝ) * (1 - theta m v i) / theta m v i at hrecBound
  have hDpos : 0 < ((K - m + 1 : ℕ) : ℝ) +
      (m : ℝ) * (1 - theta m v i) / theta m v i := by
    have hNat : 0 < K - m + 1 := by omega
    positivity
  have hrec' : 1 / q ≤
      ((K - m + 1 : ℕ) : ℝ) +
        (m : ℝ) * (1 - theta m v i) / theta m v i := by
    change 1 / q = 1 + W / v i + s * W at hrec
    exact hrec.trans_le hrecBound
  have hqD : 1 ≤ q *
      (((K - m + 1 : ℕ) : ℝ) +
        (m : ℝ) * (1 - theta m v i) / theta m v i) := by
    calc
      1 = q * (1 / q) := by field_simp [ne_of_gt hqposReal]
      _ ≤ q * (((K - m + 1 : ℕ) : ℝ) +
          (m : ℝ) * (1 - theta m v i) / theta m v i) :=
        mul_le_mul_of_nonneg_left hrec' hqpos.le
  have hqInv : 1 / (((K - m + 1 : ℕ) : ℝ) +
      (m : ℝ) * (1 - theta m v i) / theta m v i) ≤ q :=
    (div_le_iff₀ hDpos).2 hqD
  have hdenomPos : 0 < ((K - m + 1 : ℕ) : ℝ) * theta m v i +
      (m : ℝ) * (1 - theta m v i) := by
    have hNat : 0 < ((K - m + 1 : ℕ) : ℝ) := by positivity
    positivity
  have hratio :
      1 / (((K - m + 1 : ℕ) : ℝ) +
        (m : ℝ) * (1 - theta m v i) / theta m v i) =
      theta m v i /
        (((K - m + 1 : ℕ) : ℝ) * theta m v i +
          (m : ℝ) * (1 - theta m v i)) := by
    field_simp [ne_of_gt htheta, ne_of_gt hdenomPos]
  change q ≥ _
  rw [← hratio]
  exact hqInv

/-- With the anchor held at `v`, doubling every current candidate weight can
reduce its normalized conditional mass by at most a factor of two.

Both laws are the existing `conditionalFastLaw`; the proof compares its
`candidateWeight` terms and their actual `candidateNormalizer` sums.

Source: `sources/zip4/manuscript/04_slow_fast_learner.tex:24-29,49-82`. -/
theorem conditionalFastLaw_current_weight_lower_bound {K : ℕ}
    (v w : Fin K → ℝ) (U : Finset (Fin K)) (i : Fin K)
    (hv : ∀ a, 0 < v a) (hw : ∀ a, 0 < w a)
    (hvw : ∀ a, v a ≤ w a) (hwv : ∀ a, w a ≤ 2 * v a)
    (hi : i ∉ U) :
    conditionalFastLaw (Finset.univ : Finset (Fin K)) w v U
      (Finset.subset_univ U) ⟨i, by simp [hi]⟩
      (fun a _ => hw a) (fun a _ => hv a) ⟨i, by simp [hi]⟩ ≥
      conditionalFastLaw (Finset.univ : Finset (Fin K)) v v U
        (Finset.subset_univ U) ⟨i, by simp [hi]⟩
        (fun a _ => hv a) (fun a _ => hv a) ⟨i, by simp [hi]⟩ / 2 := by
  classical
  let C : Finset (Fin K) := Finset.univ \ U
  let qW : ℝ := conditionalFastLaw (Finset.univ : Finset (Fin K)) w v U
    (Finset.subset_univ U) ⟨i, by simp [hi]⟩
    (fun a _ => hw a) (fun a _ => hv a) ⟨i, by simp [hi]⟩
  let qV : ℝ := conditionalFastLaw (Finset.univ : Finset (Fin K)) v v U
    (Finset.subset_univ U) ⟨i, by simp [hi]⟩
    (fun a _ => hv a) (fun a _ => hv a) ⟨i, by simp [hi]⟩
  have hdenomPos (j : Fin K) : 0 < 1 + inverseAnchorSum v U * v j := by
    have hs := inverseAnchorSum_nonneg (Finset.univ : Finset (Fin K)) U v
      (Finset.subset_univ U) (fun a _ => hv a)
    exact add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg hs (hv j).le)
  have hcandidateLower (j : Fin K) :
      candidateWeight v v U j ≤ candidateWeight w v U j := by
    unfold candidateWeight
    exact div_le_div_of_nonneg_right (hvw j) (hdenomPos j).le
  have hcandidateUpper (j : Fin K) :
      candidateWeight w v U j ≤ 2 * candidateWeight v v U j := by
    unfold candidateWeight
    have h := div_le_div_of_nonneg_right (hwv j) (hdenomPos j).le
    calc
      w j / (1 + inverseAnchorSum v U * v j) ≤
          (2 * v j) / (1 + inverseAnchorSum v U * v j) := h
      _ = 2 * (v j / (1 + inverseAnchorSum v U * v j)) := by ring
  have hnormalizerUpper :
      candidateNormalizer (Finset.univ : Finset (Fin K)) w v U ≤
        2 * candidateNormalizer (Finset.univ : Finset (Fin K)) v v U := by
    unfold candidateNormalizer
    calc
      (∑ j ∈ C.attach, candidateWeight w v U j.1) ≤
          ∑ j ∈ C.attach, 2 * candidateWeight v v U j.1 := by
        apply Finset.sum_le_sum
        intro j hj
        exact hcandidateUpper j.1
      _ = 2 * ∑ j ∈ C.attach, candidateWeight v v U j.1 := by
        rw [Finset.mul_sum]
      _ = 2 * candidateNormalizer (Finset.univ : Finset (Fin K)) v v U := rfl
  have hnormVpos := candidateNormalizer_pos
    (Finset.univ : Finset (Fin K)) U v v (Finset.subset_univ U)
    ⟨i, by simp [hi]⟩ (fun a _ => hv a) (fun a _ => hv a)
  have hnormWpos := candidateNormalizer_pos
    (Finset.univ : Finset (Fin K)) U w v (Finset.subset_univ U)
    ⟨i, by simp [hi]⟩ (fun a _ => hw a) (fun a _ => hv a)
  have hmass :
      candidateWeight v v U i *
          candidateNormalizer (Finset.univ : Finset (Fin K)) w v U ≤
        candidateWeight w v U i *
          (2 * candidateNormalizer (Finset.univ : Finset (Fin K)) v v U) := by
    calc
      candidateWeight v v U i *
          candidateNormalizer (Finset.univ : Finset (Fin K)) w v U ≤
        candidateWeight w v U i *
          candidateNormalizer (Finset.univ : Finset (Fin K)) w v U :=
        mul_le_mul_of_nonneg_right (hcandidateLower i) hnormWpos.le
      _ ≤ candidateWeight w v U i *
          (2 * candidateNormalizer (Finset.univ : Finset (Fin K)) v v U) :=
        mul_le_mul_of_nonneg_left hnormalizerUpper
          (candidateWeight_pos (Finset.univ : Finset (Fin K)) w v U
            (Finset.subset_univ U) (fun a _ => hw a) (fun a _ => hv a)
            ⟨i, by simp [hi]⟩).le
  have hratio := (div_le_div_iff₀
      (mul_pos (by norm_num : (0 : ℝ) < 2) hnormVpos) hnormWpos).2 hmass
  change qW ≥ qV / 2
  dsimp [qW, qV]
  change candidateWeight w v U i /
      candidateNormalizer (Finset.univ : Finset (Fin K)) w v U ≥
    (candidateWeight v v U i /
      candidateNormalizer (Finset.univ : Finset (Fin K)) v v U) / 2
  calc
    candidateWeight v v U i /
        candidateNormalizer (Finset.univ : Finset (Fin K)) v v U / 2 =
      candidateWeight v v U i /
        (2 * candidateNormalizer (Finset.univ : Finset (Fin K)) v v U) := by
          field_simp [ne_of_gt hnormVpos]
    _ ≤ candidateWeight w v U i /
        candidateNormalizer (Finset.univ : Finset (Fin K)) w v U := hratio

/-- Source lower bound for the actual conditional fast law on `Fin K`, with
current weights `w` and the fixed anchor `v`.

The only assumptions are the source cardinality, positivity, and pointwise
weight comparison. The definition-domain proofs for `univ`, `U`, and the
candidate are derived internally.

Source: `sources/zip4/manuscript/04_slow_fast_learner.tex:24-46,49-82`. -/
theorem canonical_fast_conditional_lower_bound {K m : ℕ}
    (v w : Fin K → ℝ) (U : Finset (Fin K)) (i : Fin K)
    (hm : 2 ≤ m) (hmK : m < K)
    (hv : ∀ a, 0 < v a) (hw : ∀ a, 0 < w a)
    (hvw : ∀ a, v a ≤ w a) (hwv : ∀ a, w a ≤ 2 * v a)
    (hU : U.card = m - 1) (hi : i ∉ U) :
    conditionalFastLaw (Finset.univ : Finset (Fin K)) w v U
      (Finset.subset_univ U) ⟨i, by simp [hi]⟩
      (fun a _ => hw a) (fun a _ => hv a) ⟨i, by simp [hi]⟩ ≥
      theta m v i /
        (2 * (((K - m + 1 : ℕ) : ℝ) * theta m v i +
          (m : ℝ) * (1 - theta m v i))) := by
  have hstable := conditionalFastLaw_current_weight_lower_bound
    v w U i hv hw hvw hwv hi
  have hbase := conditionalFastLaw_lower_bound v U i hm hmK hv hU hi
  have hdenomPos : 0 < ((K - m + 1 : ℕ) : ℝ) * theta m v i +
      (m : ℝ) * (1 - theta m v i) := by
    have hNat : 0 < ((K - m + 1 : ℕ) : ℝ) := by positivity
    have htheta : 0 < theta m v i := theta_pos v i (by omega) hmK hv
    have hthetaOne : theta m v i < 1 := theta_lt_one v i (by omega) hmK hv
    positivity
  have hhalf :
      (theta m v i /
        (((K - m + 1 : ℕ) : ℝ) * theta m v i +
          (m : ℝ) * (1 - theta m v i))) / 2 =
      theta m v i /
        (2 * (((K - m + 1 : ℕ) : ℝ) * theta m v i +
          (m : ℝ) * (1 - theta m v i))) := by
    field_simp [ne_of_gt hdenomPos]
  calc
    conditionalFastLaw (Finset.univ : Finset (Fin K)) w v U
        (Finset.subset_univ U) ⟨i, by simp [hi]⟩
        (fun a _ => hw a) (fun a _ => hv a) ⟨i, by simp [hi]⟩ ≥
      conditionalFastLaw (Finset.univ : Finset (Fin K)) v v U
        (Finset.subset_univ U) ⟨i, by simp [hi]⟩
        (fun a _ => hv a) (fun a _ => hv a) ⟨i, by simp [hi]⟩ / 2 := hstable
    _ ≥ (theta m v i /
        (((K - m + 1 : ℕ) : ℝ) * theta m v i +
          (m : ℝ) * (1 - theta m v i))) / 2 := by
      exact div_le_div_of_nonneg_right hbase (by norm_num)
    _ = theta m v i /
        (2 * (((K - m + 1 : ℕ) : ℝ) * theta m v i +
          (m : ℝ) * (1 - theta m v i))) := hhalf

end Bandits.Support.CanonicalFastMarginalEstimate

end
