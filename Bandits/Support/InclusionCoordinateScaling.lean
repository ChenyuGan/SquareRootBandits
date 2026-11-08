module
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic
import Bandits.Support.InclusionScaling
import Mathlib.Tactic.Ring

/-!
# Inclusion rescaling on a finite law

For a normalized finite law, this file proves the exact change in the mass of
an event when its weights are multiplied by a common factor. The application
in `sources/zip4/manuscript/04_slow_fast_learner.tex:84-89` uses the resulting
bound when rescaling the weight of one coordinate. This file proves only that
finite-law rescaling step; it does not prove the other-coordinate Newton
argument in the manuscript.
-/

public section

namespace Bandits.Support.InclusionCoordinateScaling

variable {α : Type*}

/-- The mass of an inclusion predicate under a finite weight function.

The sum is restricted to `support`; values of `weight` outside that finite
support do not contribute.
-/
@[expose] def inclusionMass (support : Finset α) (weight : α → ℝ)
    (included : α → Prop) [DecidablePred included] : ℝ :=
  (support.filter included).sum weight

/-- The weight obtained by multiplying the included weights by `factor`. -/
@[expose] def rescaledWeight (weight : α → ℝ) (included : α → Prop)
    [DecidablePred included] (factor : ℝ) (x : α) : ℝ :=
  if included x then factor * weight x else weight x

/-- The total mass after rescaling the included weights. -/
@[expose] def rescaledTotalMass (support : Finset α) (weight : α → ℝ)
    (included : α → Prop) [DecidablePred included] (factor : ℝ) : ℝ :=
  support.sum (rescaledWeight weight included factor)

/-- The unnormalized included mass after rescaling. -/
@[expose] def rescaledInclusionMass (support : Finset α) (weight : α → ℝ)
    (included : α → Prop) [DecidablePred included] (factor : ℝ) : ℝ :=
  (support.filter included).sum (rescaledWeight weight included factor)

/-- The inclusion-mass quotient obtained by normalizing the rescaled finite
weights. Under the nonnegativity and factor assumptions, `rescaled_total_mass_pos`
proves that its denominator is positive. -/
@[expose] noncomputable def normalizedRescaledInclusionMass (support : Finset α)
    (weight : α → ℝ) (included : α → Prop) [DecidablePred included]
    (factor : ℝ) : ℝ :=
  rescaledInclusionMass support weight included factor /
    rescaledTotalMass support weight included factor

private theorem partition_mass (support : Finset α) (weight : α → ℝ)
    (included : α → Prop) [DecidablePred included] :
    inclusionMass support weight included +
        (support.filter (fun x => ¬ included x)).sum weight =
      support.sum weight := by
  simpa only [inclusionMass] using
    (Finset.sum_filter_add_sum_filter_not support included weight)

/-- The mass of an inclusion predicate is nonnegative when the finite law is
nonnegative on its support. -/
theorem inclusion_mass_nonneg (support : Finset α) (weight : α → ℝ)
    (included : α → Prop) [DecidablePred included]
    (hweight_nonneg : ∀ x ∈ support, 0 ≤ weight x) :
    0 ≤ inclusionMass support weight included := by
  unfold inclusionMass
  apply Finset.sum_nonneg
  intro x hx
  exact hweight_nonneg x (Finset.mem_filter.mp hx).1

/-- Under unit total mass, the inclusion mass lies in `[0,1]`.

The upper bound follows by partitioning the support into the included and
excluded parts and using nonnegativity on the excluded part.
-/
theorem inclusion_mass_mem_Icc (support : Finset α) (weight : α → ℝ)
    (included : α → Prop) [DecidablePred included]
    (hweight_nonneg : ∀ x ∈ support, 0 ≤ weight x)
    (hnormalized : support.sum weight = 1) :
    inclusionMass support weight included ∈ Set.Icc 0 1 := by
  have htheta_nonneg := inclusion_mass_nonneg support weight included hweight_nonneg
  have hrest_nonneg :
      0 ≤ (support.filter (fun x => ¬ included x)).sum weight := by
    apply Finset.sum_nonneg
    intro x hx
    exact hweight_nonneg x (Finset.mem_filter.mp hx).1
  have hpartition := partition_mass support weight included
  rw [hnormalized] at hpartition
  refine ⟨htheta_nonneg, ?_⟩
  calc
    inclusionMass support weight included ≤
        inclusionMass support weight included +
          (support.filter (fun x => ¬ included x)).sum weight :=
      le_add_of_nonneg_right hrest_nonneg
    _ = 1 := hpartition

/-- Rescaling multiplies the unnormalized included mass by the factor. -/
theorem rescaled_inclusion_mass_eq (support : Finset α) (weight : α → ℝ)
    (included : α → Prop) [DecidablePred included] (factor : ℝ) :
    rescaledInclusionMass support weight included factor =
      factor * inclusionMass support weight included := by
  unfold rescaledInclusionMass inclusionMass rescaledWeight
  calc
    (support.filter included).sum (fun x =>
        if included x then factor * weight x else weight x) =
      (support.filter included).sum (fun x => factor * weight x) := by
        apply Finset.sum_congr rfl
        intro x hx
        exact ite_eq_left (Finset.mem_filter.mp hx).2
    _ = factor * (support.filter included).sum weight := by
      rw [Finset.mul_sum]

/-- The total rescaled mass splits into the scaled included mass and the
unchanged excluded mass. -/
private theorem rescaledTotalMass_partition (support : Finset α)
    (weight : α → ℝ) (included : α → Prop) [DecidablePred included]
    (factor : ℝ) :
    rescaledTotalMass support weight included factor =
      factor * inclusionMass support weight included +
        (support.filter (fun x => ¬ included x)).sum weight := by
  unfold rescaledTotalMass
  rw [← Finset.sum_filter_add_sum_filter_not support included
    (rescaledWeight weight included factor)]
  have hIncluded :
      (support.filter included).sum (rescaledWeight weight included factor) =
        factor * inclusionMass support weight included := by
    change rescaledInclusionMass support weight included factor = _
    exact rescaled_inclusion_mass_eq support weight included factor
  have hExcluded :
      (support.filter (fun x => ¬ included x)).sum
          (rescaledWeight weight included factor) =
        (support.filter (fun x => ¬ included x)).sum weight := by
    apply Finset.sum_congr rfl
    intro x hx
    change (if included x then factor * weight x else weight x) = weight x
    exact ite_eq_right (Finset.mem_filter.mp hx).2
  rw [hIncluded, hExcluded]

/-- For a normalized nonnegative finite law, the total mass after rescaling
the included weights is `1 + (factor - 1) * θ`, where `θ` is their original
mass.

The proof partitions the finite support into the predicate and its complement,
then uses the unit-mass hypothesis to identify the complementary mass.

Source: `sources/zip4/manuscript/04_slow_fast_learner.tex:84-89`.
-/
theorem rescaled_total_mass_eq (support : Finset α) (weight : α → ℝ)
    (included : α → Prop) [DecidablePred included] (factor : ℝ)
    (hnormalized : support.sum weight = 1) :
    rescaledTotalMass support weight included factor =
      1 + (factor - 1) * inclusionMass support weight included := by
  let rest := (support.filter (fun x => ¬ included x)).sum weight
  have hpartition : inclusionMass support weight included + rest = 1 := by
    dsimp [rest]
    rw [← hnormalized]
    exact partition_mass support weight included
  have hrest : rest = 1 - inclusionMass support weight included := by
    calc
      rest = (inclusionMass support weight included + rest) -
          inclusionMass support weight included := by ring
      _ = 1 - inclusionMass support weight included := by rw [hpartition]
  calc
    rescaledTotalMass support weight included factor =
        factor * inclusionMass support weight included + rest := by
      exact rescaledTotalMass_partition support weight included factor
    _ = factor * inclusionMass support weight included +
        (1 - inclusionMass support weight included) := by rw [hrest]
    _ = 1 + (factor - 1) * inclusionMass support weight included := by ring

/-- If `factor ≥ 1`, the total rescaled mass is strictly positive. -/
theorem rescaled_total_mass_pos (support : Finset α) (weight : α → ℝ)
    (included : α → Prop) [DecidablePred included] (factor : ℝ)
    (hweight_nonneg : ∀ x ∈ support, 0 ≤ weight x)
    (hnormalized : support.sum weight = 1) (hfactor : 1 ≤ factor) :
    0 < rescaledTotalMass support weight included factor := by
  rw [rescaled_total_mass_eq support weight included factor hnormalized]
  exact Bandits.Support.InclusionScaling.denominator_pos
    (inclusion_mass_nonneg support weight included hweight_nonneg) hfactor

/-- The normalized inclusion mass after rescaling has the exact fractional
form used in the marginal argument.

Source: `sources/zip4/manuscript/04_slow_fast_learner.tex:84-89`.
-/
theorem normalized_rescaled_inclusion_mass_eq (support : Finset α)
    (weight : α → ℝ) (included : α → Prop) [DecidablePred included]
    (factor : ℝ) (hnormalized : support.sum weight = 1) :
    normalizedRescaledInclusionMass support weight included factor =
      factor * inclusionMass support weight included /
        (1 + (factor - 1) * inclusionMass support weight included) := by
  unfold normalizedRescaledInclusionMass
  rw [rescaled_inclusion_mass_eq support weight included factor,
    rescaled_total_mass_eq support weight included factor hnormalized]

/-- For `factor ≥ 1`, rescaling an event increases its normalized mass by at
most the factor.

Source: `sources/zip4/manuscript/04_slow_fast_learner.tex:84-89`.
-/
theorem normalized_rescaled_inclusion_mass_le (support : Finset α)
    (weight : α → ℝ) (included : α → Prop) [DecidablePred included]
    (factor : ℝ) (hweight_nonneg : ∀ x ∈ support, 0 ≤ weight x)
    (hnormalized : support.sum weight = 1) (hfactor : 1 ≤ factor) :
    normalizedRescaledInclusionMass support weight included factor ≤
      factor * inclusionMass support weight included := by
  rw [normalized_rescaled_inclusion_mass_eq support weight included factor
    hnormalized]
  exact Bandits.Support.InclusionScaling.scaled_inclusion_le_scaled
    (inclusion_mass_nonneg support weight included hweight_nonneg) hfactor

/-- The normalized rescaled inclusion mass remains a probability. -/
theorem normalized_rescaled_inclusion_mass_mem_Icc (support : Finset α)
    (weight : α → ℝ) (included : α → Prop) [DecidablePred included]
    (factor : ℝ) (hweight_nonneg : ∀ x ∈ support, 0 ≤ weight x)
    (hnormalized : support.sum weight = 1) (hfactor : 1 ≤ factor) :
    normalizedRescaledInclusionMass support weight included factor ∈
      Set.Icc 0 1 := by
  rw [normalized_rescaled_inclusion_mass_eq support weight included factor
    hnormalized]
  exact Bandits.Support.InclusionScaling.scaled_inclusion_mem_Icc
    (inclusion_mass_nonneg support weight included hweight_nonneg)
    (inclusion_mass_mem_Icc support weight included hweight_nonneg hnormalized).2
    hfactor

end Bandits.Support.InclusionCoordinateScaling
