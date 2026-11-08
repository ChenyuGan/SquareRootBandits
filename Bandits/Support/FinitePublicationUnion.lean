module
public import Mathlib.MeasureTheory.Measure.Basic
public import Bandits.Support.RewardMatrixCount

/-!
Finite union bounds for publication over a finite family of reward tables.

The source passage is `sources/zip4/manuscript/08_main_theorem.tex:26-65`,
especially the count of denominator-`D` reward matrices and the simultaneous
good event at lines 55-64. The per-table bad-event probability bound remains an
explicit premise here; this module proves neither Hoeffding's inequality nor
independence of the published rows.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace Bandits.Support.FinitePublicationUnion

/-- The union of bad events over a finite index family. -/
@[expose] def badEvent {Ω ι : Type*} (s : Finset ι) (bad : ι → Set Ω) : Set Ω :=
  ⋃ i ∈ s, bad i

/-- The event that every member of a finite family avoids its bad event. -/
@[expose] def goodEvent {Ω ι : Type*} (s : Finset ι) (bad : ι → Set Ω) : Set Ω :=
  {ω | ∀ i ∈ s, ω ∉ bad i}

/-- The finite-family good event is exactly the complement of the bad-event union. -/
theorem goodEvent_eq_compl_badEvent {Ω ι : Type*} (s : Finset ι) (bad : ι → Set Ω) :
    goodEvent s bad = (badEvent s bad)ᶜ := by
  ext ω
  simp [goodEvent, badEvent]

/-- Membership in the good event means that every indexed bad event is avoided. -/
theorem mem_goodEvent_iff {Ω ι : Type*} (s : Finset ι) (bad : ι → Set Ω) (ω : Ω) :
    ω ∈ goodEvent s bad ↔ ∀ i ∈ s, ω ∉ bad i := Iff.rfl

/-- A finite union of measurable bad events is measurable. -/
theorem measurableSet_badEvent {Ω ι : Type*} [MeasurableSpace Ω]
    (s : Finset ι) (bad : ι → Set Ω)
    (hmeas : ∀ i ∈ s, MeasurableSet (bad i)) :
    MeasurableSet (badEvent s bad) := by
  exact s.measurableSet_biUnion (fun i hi => hmeas i hi)

/-- If each event in a finite family has measure at most `δ`, the union has
measure at most the size of the family times `δ`. This is the finite union
bound; it assumes only the individual event bounds. -/
theorem finiteFamilyUnionBound {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (s : Finset ι) (bad : ι → Set Ω) (δ : ℝ≥0∞)
    (hprob : ∀ i ∈ s, μ (bad i) ≤ δ) :
    μ (badEvent s bad) ≤ (s.card : ℝ≥0∞) * δ := by
  calc
    μ (badEvent s bad) ≤ ∑ i ∈ s, μ (bad i) := by
      exact measure_biUnion_finset_le s bad
    _ ≤ ∑ i ∈ s, δ := Finset.sum_le_sum (fun i hi => hprob i hi)
    _ = (s.card : ℝ≥0∞) * δ := by simp

/-- The corresponding union bound over every element of a finite type. -/
theorem finiteTypeUnionBound {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) (bad : ι → Set Ω) (δ : ℝ≥0∞)
    (hprob : ∀ i, μ (bad i) ≤ δ) :
    μ (⋃ i, bad i) ≤ (Fintype.card ι : ℝ≥0∞) * δ := by
  simpa [badEvent] using
    (finiteFamilyUnionBound μ (Finset.univ : Finset ι) bad δ
      (fun i _ => hprob i))

/-- The bad-event union over all denominator-`D` reward tables. -/
@[expose] def rewardTableBadEvent {Ω : Type*} (D K T : ℕ)
    (bad : (Fin T → Fin K → Fin (D + 1)) → Set Ω) : Set Ω :=
  ⋃ r, bad r

/-- The event that every denominator-`D` reward table avoids its bad event. -/
@[expose] def rewardTableGoodEvent {Ω : Type*} (D K T : ℕ)
    (bad : (Fin T → Fin K → Fin (D + 1)) → Set Ω) : Set Ω :=
  {ω | ∀ r, ω ∉ bad r}

/-- The reward-table good event is the universal assertion over the entire finite
family of denominator-`D` tables. -/
theorem rewardTableGoodEvent_iff {Ω : Type*} (D K T : ℕ)
    (bad : (Fin T → Fin K → Fin (D + 1)) → Set Ω) (ω : Ω) :
    ω ∈ rewardTableGoodEvent D K T bad ↔
      ∀ r : Fin T → Fin K → Fin (D + 1), ω ∉ bad r := Iff.rfl

/-- Equivalently, the reward-table good event is the complement of the union of
all reward-table bad events. -/
theorem rewardTableGoodEvent_eq_compl_badEvent {Ω : Type*} (D K T : ℕ)
    (bad : (Fin T → Fin K → Fin (D + 1)) → Set Ω) :
    rewardTableGoodEvent D K T bad = (rewardTableBadEvent D K T bad)ᶜ := by
  ext ω
  simp [rewardTableGoodEvent, rewardTableBadEvent]

/-- The union over all reward tables is measurable when each constituent bad
event is measurable. -/
theorem measurableSet_rewardTableBadEvent {Ω : Type*} [MeasurableSpace Ω]
    (D K T : ℕ) (bad : (Fin T → Fin K → Fin (D + 1)) → Set Ω)
    (hmeas : ∀ r, MeasurableSet (bad r)) :
    MeasurableSet (rewardTableBadEvent D K T bad) := by
  exact MeasurableSet.iUnion hmeas

/-- Uniform individual probability bounds over denominator-`D` reward tables
give the checked finite union bound `(D + 1)^(K*T) * δ`. The exact count is
`RewardMatrixCount.rewardMatrixCount`. -/
theorem rewardTableUnionBound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (D K T : ℕ)
    (bad : (Fin T → Fin K → Fin (D + 1)) → Set Ω) (δ : ℝ≥0∞)
    (hprob : ∀ r, μ (bad r) ≤ δ) :
    μ (rewardTableBadEvent D K T bad) ≤
      (((D + 1) ^ (K * T) : ℕ) : ℝ≥0∞) * δ := by
  simpa only [rewardTableBadEvent, RewardMatrixCount.rewardMatrixCount] using
    (finiteTypeUnionBound μ bad δ hprob)

/-- Measurability of all reward-table bad events makes their good event
measurable as well. -/
theorem measurableSet_rewardTableGoodEvent {Ω : Type*} [MeasurableSpace Ω]
    (D K T : ℕ) (bad : (Fin T → Fin K → Fin (D + 1)) → Set Ω)
    (hmeas : ∀ r, MeasurableSet (bad r)) :
    MeasurableSet (rewardTableGoodEvent D K T bad) := by
  rw [rewardTableGoodEvent_eq_compl_badEvent]
  exact (measurableSet_rewardTableBadEvent D K T bad hmeas).compl

end Bandits.Support.FinitePublicationUnion
