/-
Copyright (c) 2026 Bandits Lean regret formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Probability.Moments.Basic

import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Rare-tail estimate for bounded independent variables

The source inequality is sources/zip4/manuscript/appendix_b_communication.tex:172-191.
Its indicator application to independent ID-row failure events is at
sources/zip4/manuscript/appendix_b_communication.tex:223-242.

This file proves a generic internal probability inequality. Applying it to the
identification rows still requires downstream proofs of the literal events,
their measurability and independence, and the per-row probability bound.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace Bandits.Support.RareTailBound

/-- Almost-everywhere unit-interval bounds imply integrability on a probability space. -/
theorem integrable_of_ae_mem_unitInterval {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ)
    (hX : Measurable X) (hXbound : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc (0 : ℝ) 1) :
    Integrable X μ :=
  Integrable.of_mem_Icc 0 1 hX.aemeasurable hXbound

/-- Almost-everywhere unit-interval bounds imply integrability of every exponential tilt. -/
theorem integrable_exp_mul_of_ae_mem_unitInterval {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (t : ℝ)
    (hX : Measurable X) (hXbound : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc (0 : ℝ) 1) :
    Integrable (fun ω => Real.exp (t * X ω)) μ :=
  ProbabilityTheory.integrable_exp_mul_of_mem_Icc hX.aemeasurable hXbound

/-- The convexity chord of exp between zero and a nonnegative parameter. -/
theorem exp_mul_le_unit_chord {t x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.exp (t * x) ≤ 1 + (Real.exp t - 1) * x := by
  calc
    Real.exp (t * x) = Real.exp ((1 - x) * 0 + x * t) := by congr 1; ring
    _ ≤ (1 - x) * Real.exp 0 + x * Real.exp t :=
      convexOn_exp.2 (Set.mem_univ _) (Set.mem_univ _)
        (by linarith) (by linarith) (by ring)
    _ = 1 + (Real.exp t - 1) * x := by rw [Real.exp_zero]; ring

/-- Integrating the convexity chord gives the one-variable exponential moment bound. -/
theorem integral_exp_mul_le_one_add {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (t : ℝ)
    (hX : Measurable X) (hXbound : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc (0 : ℝ) 1) :
    (∫ ω, Real.exp (t * X ω) ∂μ) ≤
      1 + (Real.exp t - 1) * (∫ ω, X ω ∂μ) := by
  have hXint := integrable_of_ae_mem_unitInterval μ X hX hXbound
  have hexpint := integrable_exp_mul_of_ae_mem_unitInterval μ X t hX hXbound
  have hlineint : Integrable (fun ω => 1 + X ω * (Real.exp t - 1)) μ :=
    (integrable_const _).add (hXint.mul_const _)
  have hpoint :
      (fun ω => Real.exp (t * X ω)) ≤ᵐ[μ]
        (fun ω => 1 + X ω * (Real.exp t - 1)) := by
    filter_upwards [hXbound] with ω hω
    calc
      Real.exp (t * X ω) ≤ 1 + (Real.exp t - 1) * X ω :=
        exp_mul_le_unit_chord hω.1 hω.2
      _ = 1 + X ω * (Real.exp t - 1) := by ring
  calc
    (∫ ω, Real.exp (t * X ω) ∂μ) ≤
        ∫ ω, (1 + X ω * (Real.exp t - 1)) ∂μ :=
      integral_mono_ae hexpint hlineint hpoint
    _ = 1 + (Real.exp t - 1) * (∫ ω, X ω ∂μ) := by
      rw [integral_add (integrable_const _) (hXint.mul_const _), integral_const,
        probReal_univ, smul_eq_mul, integral_mul_const]
      ring

/-- A finite family of independent, measurable unit-interval variables satisfies the
rare-tail inequality from the communication lemma.

The only probabilistic inputs are independence, measurability, almost-everywhere
unit-interval bounds, and the displayed sum-of-expectations bound. -/
theorem rareTailBound {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ι → Ω → ℝ)
    (h_indep : ProbabilityTheory.iIndepFun X μ)
    (h_meas : ∀ i, Measurable (X i))
    (h_bounds : ∀ i, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc (0 : ℝ) 1)
    (a ν ε : ℝ) (ha : 0 < a) (hν : 0 < ν) (hνε : ν < ε)
    (h_expectation : (∑ i, ∫ ω, X i ω ∂μ) ≤ a * ν) :
    μ.real {ω | ε < (∑ i, X i) ω / a} ≤
      Real.exp (-(a * ε) * Real.log (ε / (Real.exp 1 * ν))) := by
  let t0 : ℝ := Real.log (ε / ν)
  let S : Ω → ℝ := ∑ i, X i
  have hε : 0 < ε := hν.trans hνε
  have ht0pos : 0 < t0 := by
    apply Real.log_pos
    exact (one_lt_div hν).2 hνε
  have h_exp_t0 : Real.exp t0 = ε / ν := by
    exact Real.exp_log (div_pos hε hν)
  have h_log_endpoint :
      Real.log (ε / (Real.exp 1 * ν)) = t0 - 1 := by
    calc
      Real.log (ε / (Real.exp 1 * ν)) = Real.log ε - Real.log (Real.exp 1 * ν) :=
        Real.log_div (ne_of_gt hε) (mul_ne_zero (Real.exp_pos 1).ne' (ne_of_gt hν))
      _ = Real.log ε - (Real.log (Real.exp 1) + Real.log ν) := by
        rw [Real.log_mul (Real.exp_pos 1).ne' (ne_of_gt hν)]
      _ = (Real.log ε - Real.log ν) - 1 := by rw [Real.log_exp]; ring
      _ = t0 - 1 := by
        rw [show t0 = Real.log (ε / ν) from rfl,
          Real.log_div (ne_of_gt hε) (ne_of_gt hν)]
  have hXint : ∀ i, Integrable (X i) μ := by
    intro i
    exact integrable_of_ae_mem_unitInterval μ (X i) (h_meas i) (h_bounds i)
  have hexpint :
      ∀ i, Integrable (fun ω => Real.exp (t0 * X i ω)) μ := by
    intro i
    exact integrable_exp_mul_of_ae_mem_unitInterval μ (X i) t0 (h_meas i) (h_bounds i)
  have hexpSum : Integrable (fun ω => Real.exp (t0 * S ω)) μ := by
    have h := h_indep.integrable_exp_mul_sum (t := t0) h_meas
      (s := (Finset.univ : Finset ι)) (fun i _ => hexpint i)
    simpa [S] using h
  have hmgf_product :
      ProbabilityTheory.mgf S μ t0 =
        ∏ i ∈ (Finset.univ : Finset ι), ProbabilityTheory.mgf (X i) μ t0 := by
    have h := h_indep.mgf_sum h_meas (Finset.univ : Finset ι) (t := t0)
    simpa [S] using h
  have hc : 0 ≤ Real.exp t0 - 1 := by
    have h := Real.add_one_le_exp t0
    linarith [ht0pos]
  have hmean_nonneg : ∀ i, 0 ≤ ∫ ω, X i ω ∂μ := by
    intro i
    apply integral_nonneg_of_ae
    filter_upwards [h_bounds i] with ω hω
    exact hω.1
  have hmgf_each : ∀ i,
      ProbabilityTheory.mgf (X i) μ t0 ≤
        1 + (Real.exp t0 - 1) * (∫ ω, X i ω ∂μ) := by
    intro i
    simpa only [ProbabilityTheory.mgf] using
      (integral_exp_mul_le_one_add μ (X i) t0 (h_meas i) (h_bounds i))
  have h_expectation' :
      (∑ i ∈ (Finset.univ : Finset ι), ∫ ω, X i ω ∂μ) ≤ a * ν := by
    simpa using h_expectation
  have hmgf_bound : ProbabilityTheory.mgf S μ t0 ≤
      Real.exp ((Real.exp t0 - 1) * (a * ν)) := by
    rw [hmgf_product]
    calc
      (∏ i ∈ (Finset.univ : Finset ι), ProbabilityTheory.mgf (X i) μ t0) ≤
          ∏ i ∈ (Finset.univ : Finset ι),
            (1 + (Real.exp t0 - 1) * (∫ ω, X i ω ∂μ)) := by
        apply Finset.prod_le_prod₀
        · intro i hi
          exact ProbabilityTheory.mgf_nonneg
        · intro i hi
          exact hmgf_each i
      _ ≤ Real.exp (∑ i ∈ (Finset.univ : Finset ι),
          (Real.exp t0 - 1) * (∫ ω, X i ω ∂μ)) := by
        apply Real.prod_one_add_le_exp_sum
        intro i
        exact mul_nonneg hc (hmean_nonneg i)
      _ = Real.exp ((Real.exp t0 - 1) *
          (∑ i ∈ (Finset.univ : Finset ι), ∫ ω, X i ω ∂μ)) := by
        congr 1
        rw [← Finset.mul_sum]
      _ ≤ Real.exp ((Real.exp t0 - 1) * (a * ν)) := by
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonneg_left h_expectation' hc
  have hdiv_mul : (ε / ν) * (a * ν) = a * ε := by
    field_simp [ne_of_gt hν]
  have h_exp_exponent :
      -t0 * (a * ε) + (Real.exp t0 - 1) * (a * ν) ≤
        -(a * ε) * Real.log (ε / (Real.exp 1 * ν)) := by
    rw [h_exp_t0]
    have hnonneg : 0 ≤ a * ν := mul_nonneg ha.le hν.le
    calc
      -t0 * (a * ε) + (ε / ν - 1) * (a * ν) =
          -(a * ε) * t0 + (a * ε - a * ν) := by
            rw [sub_mul, hdiv_mul]
            ring
      _ = -(a * ε) * (t0 - 1) - a * ν := by ring
      _ ≤ -(a * ε) * (t0 - 1) := by linarith
      _ = -(a * ε) * Real.log (ε / (Real.exp 1 * ν)) := by
        rw [h_log_endpoint]
  have hsubset :
      {ω | ε < S ω / a} ⊆ {ω | a * ε ≤ S ω} := by
    intro ω hω
    have hstrict : ε * a < S ω := (lt_div_iff₀ ha).1 hω
    change a * ε ≤ S ω
    nlinarith
  have hmarkov := ProbabilityTheory.measure_ge_le_exp_mul_mgf
    (μ := μ) (X := S) (t := t0) (a * ε) ht0pos.le hexpSum
  calc
    μ.real {ω | ε < S ω / a} ≤ μ.real {ω | a * ε ≤ S ω} :=
      measureReal_mono hsubset
    _ ≤ Real.exp (-t0 * (a * ε)) * ProbabilityTheory.mgf S μ t0 := hmarkov
    _ ≤ Real.exp (-t0 * (a * ε)) *
        Real.exp ((Real.exp t0 - 1) * (a * ν)) :=
      mul_le_mul_of_nonneg_left hmgf_bound (Real.exp_pos _).le
    _ = Real.exp (-t0 * (a * ε) + (Real.exp t0 - 1) * (a * ν)) := by
      rw [← Real.exp_add]
    _ ≤ Real.exp (-(a * ε) * Real.log (ε / (Real.exp 1 * ν))) :=
      Real.exp_le_exp.mpr h_exp_exponent

/-- Chernoff bound for the number of independent rare events. The events and
their independence are explicit inputs; this specialization makes no claim
about any particular identification-row event. -/
theorem independentRareEventCount_oneQuarter {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (E : ι → Set Ω) (h_meas : ∀ i, MeasurableSet (E i))
    (h_indep : ProbabilityTheory.iIndepSet E μ)
    (ν : ℝ) (hν : 0 < ν) (hνquarter : ν < (1 / 4 : ℝ))
    (hprob : ∀ i, μ.real (E i) ≤ ν)
    (hcard : 0 < Fintype.card ι) :
    μ.real {ω |
      (1 / 4 : ℝ) <
        (∑ i : ι, (E i).indicator (fun _ : Ω => (1 : ℝ)) ω) /
          (Fintype.card ι : ℝ)} ≤
      Real.exp (-((Fintype.card ι : ℝ) * (1 / 4 : ℝ)) *
        Real.log ((1 / 4 : ℝ) / (Real.exp 1 * ν))) := by
  let Y : ι → Ω → ℝ := fun i => (E i).indicator (fun _ => (1 : ℝ))
  have hY_indep : ProbabilityTheory.iIndepFun Y μ := by
    have h : ProbabilityTheory.iIndepFun
        (fun i => (E i).indicator (fun _ : Ω => (1 : ℝ))) μ :=
      h_indep.iIndepFun_indicator
    simpa [Y] using h
  have hY_meas : ∀ i, Measurable (Y i) := by
    intro i
    exact measurable_const.indicator (h_meas i)
  have hY_bounds : ∀ i, ∀ᵐ ω ∂μ, Y i ω ∈ Set.Icc (0 : ℝ) 1 := by
    intro i
    filter_upwards [] with ω
    by_cases hω : ω ∈ E i <;> simp [Y, hω]
  have hY_expectation :
      (∑ i : ι, ∫ ω, Y i ω ∂μ) ≤ (Fintype.card ι : ℝ) * ν := by
    calc
      (∑ i : ι, ∫ ω, Y i ω ∂μ) = ∑ i : ι, μ.real (E i) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact integral_indicator_one (h_meas i)
      _ ≤ ∑ i : ι, ν := Finset.sum_le_sum fun i _ => hprob i
      _ = (Fintype.card ι : ℝ) * ν := by simp
  have htail := rareTailBound μ Y hY_indep hY_meas hY_bounds
    (Fintype.card ι : ℝ) ν (1 / 4 : ℝ)
    (Nat.cast_pos.mpr hcard) hν hνquarter hY_expectation
  simpa [Y, Finset.sum_apply] using htail

end Bandits.Support.RareTailBound

end
