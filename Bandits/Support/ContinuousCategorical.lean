/- Copyright (c) 2026. Released under Apache 2.0 license. -/
module

public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# One continuous scalar categorical draw

The inverse cumulative rule in
`sources/zip4/manuscript/appendix_b_communication.tex:34-44` uses the fixed
increasing order on `Fin n`. The strict upper comparison agrees with the
threshold convention in
`sources/zip4/manuscript/appendix_a_local_protocol.tex:66-77`.

The input is the genuine real subtype `[0,1)`, equipped with Lebesgue measure
transported to that subtype. The law is proved from half-open interval lengths.
This is generic internal mathematics, with no claim about multiple coordinates,
prefix sampling, adaptive histories, or manuscript theorem closure.
-/

public section

namespace Bandits.Support.ContinuousCategorical

open MeasureTheory Set
open scoped BigOperators ENNReal

noncomputable section

/-- A continuous scalar input, including zero and excluding one. -/
abbrev Scalar := {v : ℝ // 0 ≤ v ∧ v < 1}

theorem range_val : Set.range (Subtype.val : Scalar → ℝ) = Ico (0 : ℝ) 1 := by
  ext v
  exact ⟨fun ⟨w, hw⟩ => hw ▸ w.property, fun hv => ⟨⟨v, hv⟩, rfl⟩⟩

/-- Uniform Lebesgue measure on the genuine half-open unit interval subtype. -/
@[expose] def uniform : Measure Scalar :=
  Measure.comap (Subtype.val : Scalar → ℝ) volume

/-- Exact subtype characterization, for every set, without a measurability premise. -/
theorem uniform_apply (s : Set Scalar) :
    uniform s = volume (Subtype.val '' s : Set ℝ) :=
  comap_subtype_coe_apply measurableSet_Ico volume s

/-- The full transported measure is Lebesgue measure restricted to `[0,1)`. -/
theorem uniform_map_val :
    uniform.map (Subtype.val : Scalar → ℝ) = volume.restrict (Ico (0 : ℝ) 1) :=
  map_comap_subtype_coe measurableSet_Ico volume

/-- Exact restriction formula for the real-valued input, for every set. -/
theorem uniform_preimage_val (s : Set ℝ) :
    uniform (Subtype.val ⁻¹' s) = volume (s ∩ Ico 0 1) := by
  rw [uniform_apply, image_preimage_eq_inter_range, range_val]

theorem uniform_univ : uniform univ = 1 := by
  rw [uniform_apply, image_univ, range_val]
  exact (Real.volume_Ico).trans (by simp only [sub_zero, ENNReal.ofReal_one])

instance : IsProbabilityMeasure uniform := ⟨uniform_univ⟩

variable {n : ℕ}

/-- Cumulative mass strictly before `i`, in increasing `Fin n` order. -/
@[expose] def lower (p : Fin n → ℝ) (i : Fin n) : ℝ :=
  ∑ j ∈ Finset.Iio i, p j

/-- Cumulative mass up to and including `i`, in increasing `Fin n` order. -/
@[expose] def upper (p : Fin n → ℝ) (i : Fin n) : ℝ :=
  ∑ j ∈ Finset.Iic i, p j

theorem upper_eq_lower_add (p : Fin n → ℝ) (i : Fin n) :
    upper p i = lower p i + p i := by
  rw [upper, ← Finset.Iio_insert, Finset.sum_insert Finset.notMem_Iio_self, lower,
    add_comm]

theorem lower_nonneg {p : Fin n → ℝ} (hp : ∀ i, 0 ≤ p i) (i : Fin n) :
    0 ≤ lower p i :=
  Finset.sum_nonneg fun j _ => hp j

theorem upper_le_one {p : Fin n → ℝ} (hp : ∀ i, 0 ≤ p i)
    (hsum : ∑ i, p i = 1) (i : Fin n) : upper p i ≤ 1 := by
  rw [← hsum]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun j _ _ => hp j)

theorem upper_le_lower_of_lt {p : Fin n → ℝ} (hp : ∀ i, 0 ≤ p i)
    {i j : Fin n} (hij : i < j) : upper p i ≤ lower p j := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro k hk
    exact Finset.mem_Iio.mpr (lt_of_le_of_lt (Finset.mem_Iic.mp hk) hij)
  · intro k _ _
    exact hp k

/-- Every valid scalar crosses an upper cumulative sum; there is no default branch. -/
theorem exists_upper_gt (hn : 0 < n) {p : Fin n → ℝ}
    (hsum : ∑ i, p i = 1) (v : Scalar) : ∃ i, v.val < upper p i := by
  let last : Fin n := ⟨n - 1, by omega⟩
  have hlast : Finset.Iic last = Finset.univ := by
    ext j
    simp only [Finset.mem_Iic, Finset.mem_univ, iff_true]
    show j.val ≤ n - 1
    omega
  refine ⟨last, ?_⟩
  rw [upper, hlast, hsum]
  exact v.property.2

/-- The first strict cumulative crossing in the fixed order. Its only numerical
assumption needed for existence is the normalization; nonnegativity is required
by the interval characterization and probability law below. -/
@[expose] def sample (hn : 0 < n) (p : Fin n → ℝ)
    (hsum : ∑ i, p i = 1) (v : Scalar) : Fin n :=
  @Fin.find n (fun i => v.val < upper p i) (Classical.decPred _)
    (exists_upper_gt hn hsum v)

/-- Exact least-index characterization, including all equality cases. -/
theorem sample_eq_iff_least (hn : 0 < n) (p : Fin n → ℝ)
    (hsum : ∑ i, p i = 1) (v : Scalar) (i : Fin n) :
    sample hn p hsum v = i ↔
      v.val < upper p i ∧ ∀ j < i, upper p j ≤ v.val := by
  classical
  rw [sample, Fin.find_eq_iff]
  simp only [not_lt]

/-- Existence and uniqueness of the least strict cumulative crossing. -/
theorem exists_unique_least (hn : 0 < n) (p : Fin n → ℝ)
    (hsum : ∑ i, p i = 1) (v : Scalar) :
    ∃! i, v.val < upper p i ∧ ∀ j < i, upper p j ≤ v.val := by
  refine ⟨sample hn p hsum v, (sample_eq_iff_least hn p hsum v _).mp rfl, ?_⟩
  intro i hi
  exact ((sample_eq_iff_least hn p hsum v i).mpr hi).symm

/-- For a nonnegative mass vector, the earlier-crossing tests are equivalent to
the single inclusive lower-bound comparison. -/
theorem lower_le_iff {p : Fin n → ℝ} (hp : ∀ i, 0 ≤ p i)
    (v : Scalar) (i : Fin n) :
    lower p i ≤ v.val ↔ ∀ j < i, upper p j ≤ v.val := by
  constructor
  · intro h j hj
    exact (upper_le_lower_of_lt hp hj).trans h
  · intro h
    by_cases hi : i.val = 0
    · have hempty : Finset.Iio i = ∅ := by
        ext j
        simp only [Finset.mem_Iio, Finset.notMem_empty, iff_false]
        show ¬ j.val < i.val
        omega
      simpa only [lower, hempty, Finset.sum_empty] using v.property.1
    · let prev : Fin n := ⟨i.val - 1, by omega⟩
      have hprev : prev < i := by
        show i.val - 1 < i.val
        omega
      have heq : Finset.Iic prev = Finset.Iio i := by
        ext j
        simp only [Finset.mem_Iic, Finset.mem_Iio]
        change j.val ≤ i.val - 1 ↔ j.val < i.val
        omega
      simpa only [upper, heq, lower] using h prev hprev

/-- A draw selects precisely the half-open cumulative interval. Lower endpoints
are included; upper endpoints are excluded, even for zero masses. -/
theorem sample_eq_iff (hn : 0 < n) {p : Fin n → ℝ} (hp : ∀ i, 0 ≤ p i)
    (hsum : ∑ i, p i = 1) (v : Scalar) (i : Fin n) :
    sample hn p hsum v = i ↔ lower p i ≤ v.val ∧ v.val < upper p i := by
  rw [sample_eq_iff_least, ← lower_le_iff hp]
  exact and_comm

/-- The full fibre on the scalar subtype. -/
theorem sample_preimage_singleton (hn : 0 < n) {p : Fin n → ℝ}
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) (i : Fin n) :
    sample hn p hsum ⁻¹' {i} =
      Subtype.val ⁻¹' Ico (lower p i) (upper p i) := by
  ext v
  exact sample_eq_iff hn hp hsum v i

/-- As a set of real inputs, the fibre is exactly the cumulative interval
intersected with the input carrier. -/
theorem image_sample_fibre (hn : 0 < n) {p : Fin n → ℝ}
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) (i : Fin n) :
    Subtype.val '' (sample hn p hsum ⁻¹' {i}) =
      Ico (lower p i) (upper p i) ∩ Ico 0 1 := by
  rw [sample_preimage_singleton hn hp hsum, image_preimage_eq_inter_range, range_val]

theorem cumulative_interval_subset {p : Fin n → ℝ} (hp : ∀ i, 0 ≤ p i)
    (hsum : ∑ i, p i = 1) (i : Fin n) :
    Ico (lower p i) (upper p i) ⊆ Ico (0 : ℝ) 1 := by
  intro v hv
  exact ⟨(lower_nonneg hp i).trans hv.1, hv.2.trans_le (upper_le_one hp hsum i)⟩

/-- A zero-mass atom has an empty fibre, pointwise, not merely almost surely. -/
theorem sample_fibre_eq_empty_of_zero (hn : 0 < n) {p : Fin n → ℝ}
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) (i : Fin n) (hi : p i = 0) :
    sample hn p hsum ⁻¹' {i} = ∅ := by
  rw [sample_preimage_singleton hn hp hsum, upper_eq_lower_add, hi, add_zero,
    Ico_self, preimage_empty]

theorem measurable_sample (hn : 0 < n) {p : Fin n → ℝ}
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    Measurable (sample hn p hsum) := by
  apply measurable_to_countable'
  intro i
  rw [sample_preimage_singleton hn hp hsum]
  exact measurableSet_Ico.preimage measurable_subtype_coe

/-- Atom probabilities, derived from Lebesgue lengths of the fibres. -/
theorem uniform_sample_singleton (hn : 0 < n) {p : Fin n → ℝ}
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) (i : Fin n) :
    uniform (sample hn p hsum ⁻¹' {i}) = ENNReal.ofReal (p i) := by
  rw [uniform_apply, image_sample_fibre hn hp hsum,
    inter_eq_self_of_subset_left (cumulative_interval_subset hp hsum i),
    Real.volume_Ico, upper_eq_lower_add, add_sub_cancel_left]

/-- The finite PMF with the given real masses, including zero masses. -/
@[expose] def massPMF (p : Fin n → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hsum : ∑ i, p i = 1) : PMF (Fin n) :=
  PMF.ofFintype (fun i => ENNReal.ofReal (p i)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hp i), hsum, ENNReal.ofReal_one])

@[simp] theorem massPMF_apply (p : Fin n → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hsum : ∑ i, p i = 1) (i : Fin n) :
    massPMF p hp hsum i = ENNReal.ofReal (p i) := rfl

/-- The complete categorical law as equality to Mathlib's finite PMF measure.
No law or normalization of sampler fibres is assumed. -/
theorem uniform_map_sample (hn : 0 < n) {p : Fin n → ℝ}
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    uniform.map (sample hn p hsum) = (massPMF p hp hsum).toMeasure := by
  apply Measure.ext_of_singleton
  intro i
  rw [Measure.map_apply (measurable_sample hn hp hsum) (measurableSet_singleton i),
    uniform_sample_singleton hn hp hsum,
    PMF.toMeasure_apply_singleton _ i (measurableSet_singleton i), massPMF_apply]

end

end Bandits.Support.ContinuousCategorical
