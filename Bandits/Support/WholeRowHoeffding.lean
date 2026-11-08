module

public import Mathlib.Probability.Moments.SubGaussian

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
The finite independent-row concentration calculation used in the whole-row step
of the main theorem. The source is
`sources/zip4/manuscript/08_main_theorem.tex:26-59`.

This module proves a generic row-family inequality. It does not construct the
reference execution's complete rows or prove that their costs depend only on
their respective rows, and it makes no reward-uniform union-bound claim.
-/

@[expose] public section

namespace Bandits.Support.WholeRowHoeffding

open scoped BigOperators
open MeasureTheory

/-- The realized average of a finite family of real-valued rows. -/
noncomputable def barG {Ω : Type*} {M : ℕ} (G : Fin M → Ω → ℝ) (ω : Ω) : ℝ :=
  (∑ j : Fin M, G j ω) / (M : ℝ)

/-- The average row expectation under `μ`. -/
noncomputable def muG {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {M : ℕ}
    (G : Fin M → Ω → ℝ) : ℝ :=
  (∑ j : Fin M, ∫ ω, G j ω ∂μ) / (M : ℝ)

/-- Hoeffding's whole-row bound for an independent, bounded family.

The row-family independence, measurability, and interval bounds are explicit
inputs. In the main-theorem proof they still need to be established for the
complete reference rows before this conditional lemma applies.
-/
theorem wholeRowHoeffding {Ω : Type*} [MeasurableSpace Ω]
    {M m T : ℕ} (hM : 0 < M) (hm : 0 < m) (hT : 0 < T)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (G : Fin M → Ω → ℝ)
    (h_indep : ProbabilityTheory.iIndepFun G μ)
    (h_meas : ∀ j, AEMeasurable (G j) μ)
    (h_bounds : ∀ j, ∀ᵐ ω ∂μ,
      G j ω ∈ Set.Icc (-(m : ℝ) * (T : ℝ)) (3 * (m : ℝ) * (T : ℝ)))
    {V : ℝ} (hV : 0 ≤ V) :
    μ.real {ω | muG μ G + 2 * V < barG G ω} ≤
      Real.exp (-((M : ℝ) * V ^ 2) /
        (2 * (m : ℝ) ^ 2 * (T : ℝ) ^ 2)) := by
  have hM_real : 0 < (M : ℝ) := Nat.cast_pos.mpr hM
  have hm_real : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  have hT_real : 0 < (T : ℝ) := Nat.cast_pos.mpr hT
  have hM_ne : (M : ℝ) ≠ 0 := ne_of_gt hM_real
  have hm_ne : (m : ℝ) ≠ 0 := ne_of_gt hm_real
  have hT_ne : (T : ℝ) ≠ 0 := ne_of_gt hT_real

  have h_integrable : ∀ j, Integrable (G j) μ := by
    intro j
    exact Integrable.of_mem_Icc (-(m : ℝ) * (T : ℝ))
      (3 * (m : ℝ) * (T : ℝ)) (h_meas j) (h_bounds j)

  let c : NNReal :=
    (‖(3 * (m : ℝ) * (T : ℝ)) - (-(m : ℝ) * (T : ℝ))‖₊ / 2) ^ 2

  have h_center_indep :
      ProbabilityTheory.iIndepFun
        (fun j ω ↦ G j ω - ∫ x, G j x ∂μ) μ := by
    have h := h_indep.comp
      (fun j x ↦ x - ∫ y, G j y ∂μ)
      (fun j ↦ measurable_id.sub measurable_const)
    have h_eq :
        (fun j ω ↦ G j ω - ∫ x, G j x ∂μ) =
          (fun j ↦ (fun x ↦ x - ∫ y, G j y ∂μ) ∘ G j) := by
      funext j ω
      rfl
    rw [h_eq]
    exact h

  have h_center_subG (j : Fin M) :
      ProbabilityTheory.HasSubgaussianMGF
        (fun ω ↦ G j ω - ∫ x, G j x ∂μ) c μ := by
    simpa [c] using
      (ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc
        (h_integrable j).aemeasurable (h_bounds j))

  have h_width :
      (3 * (m : ℝ) * (T : ℝ)) - (-(m : ℝ) * (T : ℝ)) =
        4 * (m : ℝ) * (T : ℝ) := by
    ring
  have h_width_nonneg :
      0 ≤ (3 * (m : ℝ) * (T : ℝ)) - (-(m : ℝ) * (T : ℝ)) := by
    rw [h_width]
    positivity
  have h_c_value : (c : ℝ) = 4 * (m : ℝ) ^ 2 * (T : ℝ) ^ 2 := by
    change (((‖(3 * (m : ℝ) * (T : ℝ)) -
      (-(m : ℝ) * (T : ℝ))‖₊ / 2) ^ 2 : NNReal) : ℝ) = _
    rw [NNReal.coe_pow, NNReal.coe_div, coe_nnnorm]
    rw [Real.norm_of_nonneg h_width_nonneg, h_width]
    norm_num
    ring

  have htail := ProbabilityTheory.HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun
    (μ := μ) (X := fun j ω ↦ G j ω - ∫ x, G j x ∂μ)
    h_center_indep (c := fun _ : Fin M ↦ c) (s := Finset.univ)
    (by
      intro j hj
      exact h_center_subG j)
    (ε := 2 * (M : ℝ) * V) (by positivity)

  have htail' :
      μ.real {ω | 2 * (M : ℝ) * V ≤
        ∑ j : Fin M, (G j ω - ∫ x, G j x ∂μ)} ≤
        Real.exp (-(2 * (M : ℝ) * V) ^ 2 /
          (2 * ((M : ℝ) * (c : ℝ)))) := by
    simpa [Finset.sum_const, Finset.card_univ, Fintype.card_fin] using htail

  have h_mean_mul : muG μ G * (M : ℝ) =
      ∑ j : Fin M, ∫ x, G j x ∂μ := by
    unfold muG
    field_simp

  have hM_pos_for_div : 0 < (M : ℝ) := hM_real
  have h_subset :
      {ω | muG μ G + 2 * V < barG G ω} ⊆
        {ω | 2 * (M : ℝ) * V ≤
          ∑ j : Fin M, (G j ω - ∫ x, G j x ∂μ)} := by
    intro ω hω
    have h_mul :
        (muG μ G + 2 * V) * (M : ℝ) <
          ∑ j : Fin M, G j ω := by
      apply (lt_div_iff₀ hM_pos_for_div).mp
      simpa [barG] using hω
    have h_centered_sum :
        (∑ j : Fin M, (G j ω - ∫ x, G j x ∂μ)) =
          (∑ j : Fin M, G j ω) -
            (∑ j : Fin M, ∫ x, G j x ∂μ) := by
      rw [Finset.sum_sub_distrib]
    change 2 * (M : ℝ) * V ≤
      ∑ j : Fin M, (G j ω - ∫ x, G j x ∂μ)
    rw [h_centered_sum]
    nlinarith [h_mean_mul]

  have h_exp :
      -(2 * (M : ℝ) * V) ^ 2 /
          (2 * ((M : ℝ) * (c : ℝ))) =
        -((M : ℝ) * V ^ 2) /
          (2 * (m : ℝ) ^ 2 * (T : ℝ) ^ 2) := by
    rw [h_c_value]
    field_simp [hM_ne, hm_ne, hT_ne]
    ring

  calc
    μ.real {ω | muG μ G + 2 * V < barG G ω} ≤
        μ.real {ω | 2 * (M : ℝ) * V ≤
          ∑ j : Fin M, (G j ω - ∫ x, G j x ∂μ)} :=
      measureReal_mono h_subset
    _ ≤ Real.exp (-(2 * (M : ℝ) * V) ^ 2 /
          (2 * ((M : ℝ) * (c : ℝ)))) := htail'
    _ = Real.exp (-((M : ℝ) * V ^ 2) /
          (2 * (m : ℝ) ^ 2 * (T : ℝ) ^ 2)) := by rw [h_exp]

end Bandits.Support.WholeRowHoeffding
