module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Bandits.Support.PrefixSelection

/-!
# Finite prefix mass partitions

Finite mass calculations for the deterministic prefix test in
`sources/zip4/manuscript/appendix_a_local_protocol.tex:66-77`. These statements
concern finite sums and branch positivity only; they do not assert a sampler
pushforward or measurability result.
-/

public section

namespace Bandits.Support.PrefixMassPartition

variable {α : Type*}

/-- The total mass on a finite candidate support. -/
@[expose] def totalMass (support : Finset α) (weight : α → ℝ) : ℝ :=
  ∑ a ∈ support, weight a

/-- The mass of candidates satisfying the next-arm inclusion predicate. -/
@[expose] def includedMass (support : Finset α) (weight : α → ℝ)
    (selected : α → Prop) [DecidablePred selected] : ℝ :=
  ∑ a ∈ support with selected a, weight a

/-- The mass of candidates excluded by the next-arm inclusion predicate. -/
@[expose] def excludedMass (support : Finset α) (weight : α → ℝ)
    (selected : α → Prop) [DecidablePred selected] : ℝ :=
  ∑ a ∈ support with ¬ selected a, weight a

/-- Splitting a finite support by the next-arm predicate partitions its mass. -/
theorem totalMass_eq_included_add_excluded (support : Finset α) (weight : α → ℝ)
    (selected : α → Prop) [DecidablePred selected] :
    totalMass support weight =
      includedMass support weight selected + excludedMass support weight selected := by
  unfold totalMass includedMass excludedMass
  exact (Finset.sum_filter_add_sum_filter_not support selected weight).symm

/-- Nonnegative candidate weights give nonnegative mass on the included filter. -/
theorem includedMass_nonneg (support : Finset α) (weight : α → ℝ)
    (selected : α → Prop) [DecidablePred selected]
    (hweight : ∀ a ∈ support, 0 ≤ weight a) :
    0 ≤ includedMass support weight selected := by
  unfold includedMass
  apply Finset.sum_nonneg
  intro a ha
  exact hweight a (Finset.mem_filter.mp ha).1

/-- Nonnegative candidate weights give nonnegative mass on the excluded filter. -/
theorem excludedMass_nonneg (support : Finset α) (weight : α → ℝ)
    (selected : α → Prop) [DecidablePred selected]
    (hweight : ∀ a ∈ support, 0 ≤ weight a) :
    0 ≤ excludedMass support weight selected := by
  unfold excludedMass
  apply Finset.sum_nonneg
  intro a ha
  exact hweight a (Finset.mem_filter.mp ha).1

/-- The included mass lies between zero and the total mass. -/
theorem includedMass_bounds (support : Finset α) (weight : α → ℝ)
    (selected : α → Prop) [DecidablePred selected]
    (hweight : ∀ a ∈ support, 0 ≤ weight a) :
    0 ≤ includedMass support weight selected ∧
      includedMass support weight selected ≤ totalMass support weight := by
  constructor
  · exact includedMass_nonneg support weight selected hweight
  · calc
      includedMass support weight selected ≤
          includedMass support weight selected + excludedMass support weight selected :=
        le_add_of_nonneg_right (excludedMass_nonneg support weight selected hweight)
      _ = totalMass support weight :=
        (totalMass_eq_included_add_excluded support weight selected).symm

/-- The mass of the excluded filter is total mass minus included mass. -/
theorem excludedMass_eq_totalMass_sub_includedMass (support : Finset α)
    (weight : α → ℝ) (selected : α → Prop) [DecidablePred selected] :
    excludedMass support weight selected =
      totalMass support weight - includedMass support weight selected := by
  calc
    excludedMass support weight selected =
        (includedMass support weight selected + excludedMass support weight selected) -
          includedMass support weight selected := by
      rw [add_comm]
      exact (add_sub_cancel_right _ _).symm
    _ = totalMass support weight - includedMass support weight selected := by
      rw [← totalMass_eq_included_add_excluded support weight selected]

/-- A positive finite filtered sum cannot come from an empty filtered support. -/
theorem includedSupport_nonempty_of_mass_pos (support : Finset α) (weight : α → ℝ)
    (selected : α → Prop) [DecidablePred selected]
    (hmass : 0 < includedMass support weight selected) :
    (support.filter selected).Nonempty := by
  by_contra hempty
  have hzero : includedMass support weight selected = 0 := by
    unfold includedMass
    apply Finset.sum_eq_zero
    intro a ha
    exact (hempty ⟨a, ha⟩).elim
  linarith

/-- A positive complementary filtered sum cannot come from an empty filtered support. -/
theorem excludedSupport_nonempty_of_mass_pos (support : Finset α) (weight : α → ℝ)
    (selected : α → Prop) [DecidablePred selected]
    (hmass : 0 < excludedMass support weight selected) :
    (support.filter (fun a => ¬ selected a)).Nonempty := by
  by_contra hempty
  have hzero : excludedMass support weight selected = 0 := by
    unfold excludedMass
    apply Finset.sum_eq_zero
    intro a ha
    exact (hempty ⟨a, ha⟩).elim
  linarith

/--
The strict threshold branch and its complement each carry positive mass when
the current total is positive and the threshold value is in `[0,1)`. The
rejection premise is the negation of the strict comparison, so equality is
handled by the excluded filter.
-/
theorem thresholdBranches_have_positive_mass (support : Finset α) (weight : α → ℝ)
    (selected : α → Prop) [DecidablePred selected] (v : ℝ)
    (hW : 0 < totalMass support weight)
    (hv_nonneg : 0 ≤ v) (hv_lt_one : v < 1) :
    (v * totalMass support weight < includedMass support weight selected →
      0 < includedMass support weight selected) ∧
    (¬ v * totalMass support weight < includedMass support weight selected →
      0 < excludedMass support weight selected) := by
  have hbranches := PrefixSelection.prefixBranchHasPositiveMass
    (W := totalMass support weight) (Win := includedMass support weight selected)
    hW hv_nonneg hv_lt_one
  constructor
  · exact hbranches.1
  · intro hreject
    rw [excludedMass_eq_totalMass_sub_includedMass]
    exact hbranches.2 hreject

/-- Equality with the threshold is rejected, and its complementary filtered mass is positive. -/
theorem thresholdEquality_goes_to_excluded (support : Finset α) (weight : α → ℝ)
    (selected : α → Prop) [DecidablePred selected] (v : ℝ)
    (hW : 0 < totalMass support weight)
    (hv_nonneg : 0 ≤ v) (hv_lt_one : v < 1)
    (heq : includedMass support weight selected = v * totalMass support weight) :
    0 < excludedMass support weight selected := by
  apply (thresholdBranches_have_positive_mass support weight selected v hW
    hv_nonneg hv_lt_one).2
  rw [heq]
  exact not_lt_of_ge le_rfl

end Bandits.Support.PrefixMassPartition

end
