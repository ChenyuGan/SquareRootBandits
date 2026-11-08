/- A finite probability mass function from strictly positive weights. -/
module

public import Bandits.Support.FiniteNormalization
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Probability mass functions from positive finite weights

For a nonempty finite support, strictly positive real weights determine a PMF on
the support subtype by dividing each weight by its total mass. This is the
finite set-distribution construction in
`sources/zip4/manuscript/04_slow_fast_learner.tex:7-37`; its carrier contains
only support elements.
-/

public section

namespace Bandits.Support.PositiveWeightPMF

open ENNReal Finset
open Bandits.Support.FiniteNormalization

variable {α : Type*}

/-- The PMF obtained by normalizing positive real weights on a nonempty finite
support. Its carrier is the subtype of elements of that support. -/
@[expose] noncomputable def ofPositiveWeights (support : Finset α) (weight : α → ℝ)
    (hsupport : support.Nonempty) (hweight : ∀ i ∈ support, 0 < weight i) :
    PMF {i // i ∈ support} := by
  refine PMF.ofFinset
    (fun i : {i // i ∈ support} => ENNReal.ofReal (normalizedWeight support weight i.val))
    support.attach ?_ ?_
  · calc
      (∑ i ∈ support.attach,
          ENNReal.ofReal (normalizedWeight support weight i.val)) =
          ∑ i ∈ support, ENNReal.ofReal (normalizedWeight support weight i) := by
            exact support.sum_attach
              (f := fun i => ENNReal.ofReal (normalizedWeight support weight i))
      _ = ENNReal.ofReal (∑ i ∈ support, normalizedWeight support weight i) := by
            symm
            apply ENNReal.ofReal_sum_of_nonneg
            intro i hi
            exact (div_pos (hweight i hi)
              (totalMass_pos support weight hsupport hweight)).le
      _ = 1 := by
            rw [sum_normalizedWeight_eq_one support weight hsupport hweight]
            simp
  · intro i hi
    exact False.elim (hi (Finset.mem_attach support i))

/-- Pointwise, the constructed PMF is the weight divided by total mass. -/
theorem ofPositiveWeights_apply (support : Finset α) (weight : α → ℝ)
    (hsupport : support.Nonempty) (hweight : ∀ i ∈ support, 0 < weight i)
    (i : {i // i ∈ support}) :
    ofPositiveWeights support weight hsupport hweight i =
      ENNReal.ofReal (weight i.val / totalMass support weight) := by
  simp [ofPositiveWeights, normalizedWeight]

/-- Every atom in the support subtype has strictly positive PMF mass. -/
theorem ofPositiveWeights_apply_pos (support : Finset α) (weight : α → ℝ)
    (hsupport : support.Nonempty) (hweight : ∀ i ∈ support, 0 < weight i)
    (i : {i // i ∈ support}) : 0 < ofPositiveWeights support weight hsupport hweight i := by
  rw [ofPositiveWeights_apply]
  exact ENNReal.ofReal_pos.mpr
    (div_pos (hweight i.val i.property) (totalMass_pos support weight hsupport hweight))

end Bandits.Support.PositiveWeightPMF
