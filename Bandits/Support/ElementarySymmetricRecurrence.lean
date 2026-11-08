/- Elementary symmetric sums over finite sets of weighted coordinates. -/
module
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs

/-!
# Elementary symmetric sums on finite sets

The definition is the finite subset formula used in
`sources/zip4/manuscript/04_slow_fast_learner.tex:7-13`.  The results here are
supporting identities and positivity facts; they do not close a manuscript
claim.  The insertion formula also supports the elementary symmetric sum
identity used in `sources/zip4/manuscript/04_slow_fast_learner.tex:84-89`.
-/

public section

namespace Bandits.Support.ElementarySymmetricRecurrence

variable {α : Type*}

/-- The degree-`k` elementary symmetric sum of the weights on `I`. -/
@[expose] def elementarySymmetric (w : α → ℝ) (I : Finset α) (k : ℕ) : ℝ :=
  (I.powersetCard k).sum fun t => t.prod w

/-- The source-literal finite formula agrees with Mathlib's multiset `esymm`. -/
theorem elementarySymmetric_eq_multiset_esymm (w : α → ℝ) (I : Finset α) (k : ℕ) :
    elementarySymmetric w I k = (I.val.map w).esymm k := by
  unfold elementarySymmetric
  exact (Finset.esymm_map_val w I k).symm

/-- The degree-zero elementary symmetric sum is one. -/
@[simp] theorem elementarySymmetric_zero (w : α → ℝ) (I : Finset α) :
    elementarySymmetric w I 0 = 1 := by
  simp [elementarySymmetric]

/-- A degree larger than the support cardinality has no terms. -/
theorem elementarySymmetric_eq_zero_of_card_lt (w : α → ℝ) (I : Finset α) {k : ℕ}
    (hk : I.card < k) : elementarySymmetric w I k = 0 := by
  unfold elementarySymmetric
  rw [Finset.powersetCard_eq_empty.mpr hk]
  simp

/-- Inserting a fresh coordinate splits subsets according to whether they contain it. -/
theorem elementarySymmetric_insert_succ [DecidableEq α] (w : α → ℝ) (I : Finset α) (j : α)
    (hj : j ∉ I) (k : ℕ) :
    elementarySymmetric w (insert j I) (k + 1) =
      elementarySymmetric w I (k + 1) + w j * elementarySymmetric w I k := by
  classical
  have hdisj : Disjoint (I.powersetCard (k + 1))
      ((I.powersetCard k).image (fun t : Finset α => insert j t)) := by
    rw [Finset.disjoint_left]
    intro t ht htImage
    obtain ⟨u, hu, htu⟩ := Finset.mem_image.mp htImage
    have hjt : j ∈ t := by rw [← htu]; exact Finset.mem_insert_self j u
    exact hj ((Finset.mem_powersetCard.mp ht).1 hjt)
  have hinj : ∀ ⦃u⦄, u ∈ I.powersetCard k → ∀ ⦃v⦄,
      v ∈ I.powersetCard k → insert j u = insert j v → u = v := by
    intro u hu v hv huv
    have hju : j ∉ u := fun hju => hj ((Finset.mem_powersetCard.mp hu).1 hju)
    have hjv : j ∉ v := fun hjv => hj ((Finset.mem_powersetCard.mp hv).1 hjv)
    have herase := congrArg (fun s : Finset α => s.erase j) huv
    simpa [Finset.erase_insert hju, Finset.erase_insert hjv] using herase
  rw [elementarySymmetric, Finset.powersetCard_succ_insert hj k,
    Finset.sum_union hdisj, Finset.sum_image hinj]
  have hnotmem : ∀ t ∈ I.powersetCard k, j ∉ t := by
    intro t ht hmem
    exact hj ((Finset.mem_powersetCard.mp ht).1 hmem)
  have hsum :
      ((I.powersetCard k).sum fun t => (insert j t).prod w) =
        w j * elementarySymmetric w I k := by
    calc
      ((I.powersetCard k).sum fun t => (insert j t).prod w) =
          (I.powersetCard k).sum fun t => w j * t.prod w := by
            apply Finset.sum_congr rfl
            intro t ht
            rw [Finset.prod_insert (hnotmem t ht)]
      _ = w j * (I.powersetCard k).sum (fun t => t.prod w) := by
        rw [← Finset.mul_sum]
      _ = w j * elementarySymmetric w I k := rfl
  change (I.powersetCard (k + 1)).sum (fun t => t.prod w) +
      ((I.powersetCard k).sum fun t => (insert j t).prod w) = _
  rw [hsum]
  rfl

/-- Nonnegative weights give a nonnegative elementary symmetric sum in every degree. -/
theorem elementarySymmetric_nonneg (w : α → ℝ) (I : Finset α) (k : ℕ)
    (hw : ∀ i ∈ I, 0 ≤ w i) : 0 ≤ elementarySymmetric w I k := by
  unfold elementarySymmetric
  apply Finset.sum_nonneg
  intro t ht
  apply Finset.prod_nonneg
  intro i hi
  exact hw i ((Finset.mem_powersetCard.mp ht).1 hi)

/-- Positive weights give a positive sum whenever the requested degree exists. -/
theorem elementarySymmetric_pos (w : α → ℝ) (I : Finset α) (k : ℕ)
    (hw : ∀ i ∈ I, 0 < w i) (hk : k ≤ I.card) :
    0 < elementarySymmetric w I k := by
  unfold elementarySymmetric
  apply Finset.sum_pos
  · intro t ht
    apply Finset.prod_pos
    intro i hi
    exact hw i ((Finset.mem_powersetCard.mp ht).1 hi)
  · exact Finset.powersetCard_nonempty.mpr hk

end Bandits.Support.ElementarySymmetricRecurrence
