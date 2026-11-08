/- Finite normalization helpers for positive weights. -/
module
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Field

/-!
# Finite normalization for positive weights

These generic finite-sum helpers formalize the normalization underlying the set
weights introduced in `sources/zip4/manuscript/04_slow_fast_learner.tex:7-40`.
They are internal mathematical tools and do not close a source-facing claim.
-/

public section

namespace Bandits.Support.FiniteNormalization

variable {α : Type*}

/-- The total weight carried by a finite support. -/
@[expose] def totalMass (support : Finset α) (weight : α → ℝ) : ℝ :=
  ∑ i ∈ support, weight i

/-- The normalized weight of an element, relative to a finite support. -/
@[expose] noncomputable def normalizedWeight (support : Finset α) (weight : α → ℝ)
    (i : α) : ℝ :=
  weight i / totalMass support weight

/-- The normalized mass assigned to a finite subset. -/
@[expose] noncomputable def mass (support : Finset α) (weight : α → ℝ)
    (subset : Finset α) : ℝ :=
  ∑ i ∈ subset, normalizedWeight support weight i

/-- Strictly positive weights on a nonempty finite support have positive total mass. -/
theorem totalMass_pos (support : Finset α) (weight : α → ℝ)
    (hsupport : support.Nonempty) (hweight : ∀ i ∈ support, 0 < weight i) :
    0 < totalMass support weight := by
  unfold totalMass
  exact Finset.sum_pos hweight hsupport

/-- Normalizing positive weights makes their sum over the support equal to one. -/
theorem sum_normalizedWeight_eq_one (support : Finset α) (weight : α → ℝ)
    (hsupport : support.Nonempty) (hweight : ∀ i ∈ support, 0 < weight i) :
    (∑ i ∈ support, normalizedWeight support weight i) = 1 := by
  unfold normalizedWeight
  rw [← Finset.sum_div]
  change totalMass support weight / totalMass support weight = 1
  exact div_self (ne_of_gt (totalMass_pos support weight hsupport hweight))

/-- The mass of the empty subset is zero. -/
theorem mass_empty (support : Finset α) (weight : α → ℝ) :
    mass support weight ∅ = 0 := by
  simp [mass]

/-- Every nonempty subset of the support has positive normalized mass. -/
theorem mass_pos (support subset : Finset α) (weight : α → ℝ)
    (hsubset : subset ⊆ support) (hsubset_nonempty : subset.Nonempty)
    (hweight : ∀ i ∈ support, 0 < weight i) :
    0 < mass support weight subset := by
  have hsupport : support.Nonempty := by
    obtain ⟨i, hi⟩ := hsubset_nonempty
    exact ⟨i, hsubset hi⟩
  unfold mass normalizedWeight
  apply Finset.sum_pos
  · intro i hi
    exact div_pos (hweight i (hsubset hi))
      (totalMass_pos support weight hsupport hweight)
  · exact hsubset_nonempty

end Bandits.Support.FiniteNormalization
