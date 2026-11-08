/-
Copyright (c) 2026 Bandits Lean formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Probability.ConditionalProbability
public import Mathlib.Probability.Kernel.Defs

/-!
# Lifting a finite outcome to its measurable fibre

This internal construction supplies the measure-theoretic finite-fibre step in
`sources/zip4/manuscript/06_interruptions.tex:410-423`. For an already measurable
sampler `F` and a probability measure `μ`, its outcome masses are defined by
`μ (F ⁻¹' {a})`. On a positive-mass fibre the lifting measure is the normalized
restriction of `μ`; on a null fibre it is `μ` itself, using the arbitrary branch
explicitly permitted in the source. The resulting kernel is a Markov kernel,
and its mixture is exactly `μ` as a measure on the entire input space.

No sampler measurability, pushforward calculation, or independence from an
adaptive history is supplied by this module. Those application obligations
must be proved before interpreting this construction as the source conditional
law. In particular, the mixture identity preserves a full vector distribution
when the input space is a continuous cube, rather than just its coordinates.
-/

public section

namespace Bandits.Support.FiniteFibreLift

open MeasureTheory
open scoped ENNReal BigOperators

variable {Ω α : Type*} [MeasurableSpace Ω]

/-- The input points producing outcome `a`. -/
@[expose] def fibre (F : Ω → α) (a : α) : Set Ω := F ⁻¹' {a}

/-- The mass of an outcome is derived from its fibre, not supplied separately. -/
@[expose] noncomputable def fibreMass (μ : Measure Ω) (F : Ω → α) (a : α) : ℝ≥0∞ :=
  μ (fibre F a)

/-- Normalized restriction on nonnull fibres; the original law on null fibres. -/
@[expose] noncomputable def fibreMeasure (μ : Measure Ω) (F : Ω → α) (a : α) :
    Measure Ω :=
  if fibreMass μ F a = 0 then μ
  else (fibreMass μ F a)⁻¹ • μ.restrict (fibre F a)

variable (μ : Measure Ω) (F : Ω → α) (a : α)

/-- The explicit null-fibre convention. -/
theorem fibreMeasure_of_eq_zero (ha : fibreMass μ F a = 0) :
    fibreMeasure μ F a = μ := by
  simp only [fibreMeasure, ite_eq_left ha]

/-- The defining normalized-restriction formula on a nonnull fibre. -/
theorem fibreMeasure_of_ne_zero (ha : fibreMass μ F a ≠ 0) :
    fibreMeasure μ F a = (fibreMass μ F a)⁻¹ • μ.restrict (fibre F a) := by
  simp only [fibreMeasure, ite_eq_right ha]

/-- Fibre masses are finite whenever the original measure is finite. -/
theorem fibreMass_ne_top [IsFiniteMeasure μ] : fibreMass μ F a ≠ ∞ :=
  measure_ne_top μ (fibre F a)

/-- Probability status follows from normalization, including the null branch. -/
instance instIsProbabilityMeasureFibreMeasure [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (fibreMeasure μ F a) := by
  classical
  by_cases ha : fibreMass μ F a = 0
  · rw [fibreMeasure_of_eq_zero μ F a ha]
    infer_instance
  · rw [fibreMeasure_of_ne_zero μ F a ha]
    change IsProbabilityMeasure (ProbabilityTheory.cond μ (fibre F a))
    exact ProbabilityTheory.cond_isProbabilityMeasure ha

/-- Evaluation on a measurable event is the fibre-intersection ratio.
Only a nonnull fibre and measurability of the event are needed for this formula. -/
theorem fibreMeasure_apply (ha : fibreMass μ F a ≠ 0)
    {C : Set Ω} (hC : MeasurableSet C) :
    fibreMeasure μ F a C = μ (C ∩ fibre F a) / fibreMass μ F a := by
  rw [fibreMeasure_of_ne_zero μ F a ha, Measure.smul_apply,
    Measure.restrict_apply hC, smul_eq_mul, ENNReal.div_eq_inv_mul]

/-- Multiplying by the derived mass recovers the restricted measure even on
null fibres. This cancellation needs finiteness, not a probability premise. -/
theorem fibreMass_smul_fibreMeasure [IsFiniteMeasure μ] :
    fibreMass μ F a • fibreMeasure μ F a = μ.restrict (fibre F a) := by
  classical
  by_cases ha : fibreMass μ F a = 0
  · rw [ha, zero_smul]
    exact (Measure.restrict_eq_zero.mpr ha).symm
  · rw [fibreMeasure_of_ne_zero μ F a ha, smul_smul,
      ENNReal.mul_inv_cancel ha (fibreMass_ne_top μ F a), one_smul]

section MeasurableSampler

variable [MeasurableSpace α] [MeasurableSingletonClass α]

/-- Measurability of the sampler makes each fibre measurable. -/
theorem measurableSet_fibre (hF : Measurable F) : MeasurableSet (fibre F a) :=
  hF (measurableSet_singleton a)

/-- The lifting measure gives its own positive-mass fibre probability one. -/
theorem fibreMeasure_fibre [IsFiniteMeasure μ] (hF : Measurable F)
    (ha : fibreMass μ F a ≠ 0) : fibreMeasure μ F a (fibre F a) = 1 := by
  rw [fibreMeasure_apply μ F a ha (measurableSet_fibre F a hF), Set.inter_self]
  exact ENNReal.div_self ha (fibreMass_ne_top μ F a)

/-- Sampling the lifted input recovers the chosen outcome almost surely on
every positive-mass fibre. No such assertion is imposed on null fibres. -/
theorem ae_fibreMeasure_eq (hF : Measurable F) (ha : fibreMass μ F a ≠ 0) :
    ∀ᵐ v ∂fibreMeasure μ F a, F v = a := by
  rw [fibreMeasure_of_ne_zero μ F a ha]
  exact Measure.ae_smul_measure (ae_restrict_mem (measurableSet_fibre F a hF)) _

variable [Fintype α]

/-- All fibre restrictions form the original measure, by the finite measurable
partition associated with the sampler. -/
theorem sum_restrict_fibre (hF : Measurable F) :
    (∑ a, μ.restrict (fibre F a)) = μ := by
  have hcover : (⋃ a, fibre F a) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro v
    exact Set.mem_iUnion.mpr ⟨F v, rfl⟩
  have hpartition : μ.restrict (⋃ a, fibre F a) =
      Measure.sum (fun a => μ.restrict (fibre F a)) := Measure.restrict_iUnion (μ := μ)
    (pairwise_disjoint_fiber F) (fun a => measurableSet_fibre F a hF)
  rw [hcover, Measure.restrict_univ, Measure.sum_fintype] at hpartition
  exact hpartition.symm

/-- The outcome masses sum to one as a consequence of the measurable partition. -/
theorem sum_fibreMass [IsProbabilityMeasure μ] (hF : Measurable F) :
    (∑ a, fibreMass μ F a) = 1 := by
  have h := congrArg (fun ν : Measure Ω => ν Set.univ) (sum_restrict_fibre μ F hF)
  simpa only [Measure.finsetSum_apply, Measure.restrict_apply_univ,
    fibreMass, measure_univ] using h

/-- Exact equality of full measures: sample an outcome using its derived mass,
then sample its fibre measure. No mixture or normalization premise is assumed. -/
theorem sum_fibreMass_smul_fibreMeasure [IsProbabilityMeasure μ] (hF : Measurable F) :
    (∑ a, fibreMass μ F a • fibreMeasure μ F a) = μ := by
  simp_rw [fibreMass_smul_fibreMeasure]
  exact sum_restrict_fibre μ F hF

/-- Event evaluation of the full marginal identity, valid even for events that
have not been assumed measurable because the underlying measures are equal. -/
theorem sum_fibreMass_mul_fibreMeasure [IsProbabilityMeasure μ] (hF : Measurable F)
    (C : Set Ω) : (∑ a, fibreMass μ F a * fibreMeasure μ F a C) = μ C := by
  have h := congrArg (fun ν : Measure Ω => ν C)
    (sum_fibreMass_smul_fibreMeasure μ F hF)
  simpa only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul] using h

/-- The finite discrete outcome space makes the family of lifting measures a
measurable kernel. Its definition does not presuppose sampler measurability. -/
@[expose] noncomputable def fibreKernel : ProbabilityTheory.Kernel α Ω where
  toFun := fibreMeasure μ F
  measurable' := measurable_of_finite _

/-- Evaluation of the bundled kernel exposes the literal lifting measure. -/
@[simp] theorem fibreKernel_apply : fibreKernel μ F a = fibreMeasure μ F a := rfl

/-- Every row of the lifting kernel is a probability measure. -/
instance instIsMarkovKernelFibreKernel [IsProbabilityMeasure μ] :
    ProbabilityTheory.IsMarkovKernel (fibreKernel μ F) where
  isProbabilityMeasure a := instIsProbabilityMeasureFibreMeasure μ F a

/-- The bundled Markov kernel has the original full input measure as marginal. -/
theorem sum_fibreMass_smul_fibreKernel [IsProbabilityMeasure μ] (hF : Measurable F) :
    (∑ a, fibreMass μ F a • fibreKernel μ F a) = μ :=
  sum_fibreMass_smul_fibreMeasure μ F hF

end MeasurableSampler

end Bandits.Support.FiniteFibreLift
