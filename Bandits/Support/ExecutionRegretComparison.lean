/-
Copyright (c) 2026 Bandits contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Real

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Integral comparison outside exceptional execution events

This module proves the generic measure-theoretic comparison used by the
actual/reference reward argument in
`sources/zip4/manuscript/08_main_theorem.tex:67-75`; the common-comparator
subtraction is the arithmetic in line 68. Lines 163-168 give a separate,
pathwise rounded-matrix regret comparison and are cited as surrounding source
context, not as a result proved here.

The measurable exceptional events, almost-everywhere equality away from their
union, and bounded integrable reward functions are explicit inputs. This module
does not construct the actual/reference coupling, prove measurability of its
policies or events, or establish the main regret theorem.
-/

@[expose] public section

open MeasureTheory

namespace Bandits.Support.ExecutionRegretComparison

/-- If two integrable rewards lie in `[0,B]` almost everywhere and agree away
from two measurable exceptional events, their expected rewards differ by at
most `B` times the sum of those event probabilities.

Source comparison: `sources/zip4/manuscript/08_main_theorem.tex:67-75`. -/
theorem integral_difference_abs_le_bad_event_mass
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F G : Ω → ℝ)
    (hF_int : Integrable F μ) (hG_int : Integrable G μ)
    (B : ℝ) (hB : 0 ≤ B)
    (E Eforward : Set Ω)
    (hE : MeasurableSet E) (hEforward : MeasurableSet Eforward)
    (hF_bounds : ∀ᵐ x ∂μ, F x ∈ Set.Icc (0 : ℝ) B)
    (hG_bounds : ∀ᵐ x ∂μ, G x ∈ Set.Icc (0 : ℝ) B)
    (h_eq_off_bad : ∀ᵐ x ∂μ, x ∉ (E ∪ Eforward) → F x = G x) :
    |(∫ x, F x ∂μ) - (∫ x, G x ∂μ)| ≤
      B * (μ.real E + μ.real Eforward) := by
  let bad : Set Ω := E ∪ Eforward
  have hbad : MeasurableSet bad := hE.union hEforward
  have hdiff_bound : ∀ᵐ x ∂μ,
      |F x - G x| ≤ bad.indicator (fun _ : Ω => B) x := by
    filter_upwards [hF_bounds, hG_bounds, h_eq_off_bad] with x hFx hGx heq
    by_cases hmem : x ∈ bad
    · rw [Set.indicator_of_mem hmem]
      exact abs_le.mpr ⟨by linarith [hFx.1, hFx.2, hGx.1, hGx.2],
        by linarith [hFx.1, hFx.2, hGx.1, hGx.2]⟩
    · rw [Set.indicator_of_notMem hmem]
      have hEq := heq hmem
      simp [hEq]

  have hdiff_int : Integrable (fun x => F x - G x) μ := hF_int.sub hG_int
  have habs_int : Integrable (fun x => |F x - G x|) μ := hdiff_int.abs
  have hindicator_int : Integrable (bad.indicator (fun _ : Ω => B)) μ :=
    (integrable_const B).indicator hbad
  have hindicator_integral :
      (∫ x, bad.indicator (fun _ : Ω => B) x ∂μ) = B * μ.real bad := by
    rw [integral_indicator_const B hbad, smul_eq_mul]
    ring
  have hbad_measure : μ.real bad ≤ μ.real E + μ.real Eforward := by
    exact measureReal_union_le E Eforward

  calc
    |(∫ x, F x ∂μ) - (∫ x, G x ∂μ)| =
        |∫ x, (F x - G x) ∂μ| := by rw [integral_sub hF_int hG_int]
    _ ≤ ∫ x, |F x - G x| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ x, bad.indicator (fun _ : Ω => B) x ∂μ :=
      integral_mono_ae habs_int hindicator_int hdiff_bound
    _ = B * μ.real bad := hindicator_integral
    _ ≤ B * (μ.real E + μ.real Eforward) :=
      mul_le_mul_of_nonneg_left hbad_measure hB

/-- The two signed forms of the exceptional-event reward comparison.

The left inequality is the reverse integral comparison and the right
inequality is the forward comparison. -/
theorem integral_difference_bounds_bad_event_mass
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F G : Ω → ℝ)
    (hF_int : Integrable F μ) (hG_int : Integrable G μ)
    (B : ℝ) (hB : 0 ≤ B)
    (E Eforward : Set Ω)
    (hE : MeasurableSet E) (hEforward : MeasurableSet Eforward)
    (hF_bounds : ∀ᵐ x ∂μ, F x ∈ Set.Icc (0 : ℝ) B)
    (hG_bounds : ∀ᵐ x ∂μ, G x ∈ Set.Icc (0 : ℝ) B)
    (h_eq_off_bad : ∀ᵐ x ∂μ, x ∉ (E ∪ Eforward) → F x = G x) :
    -(B * (μ.real E + μ.real Eforward)) ≤
        (∫ x, F x ∂μ) - (∫ x, G x ∂μ) ∧
      (∫ x, F x ∂μ) - (∫ x, G x ∂μ) ≤
        B * (μ.real E + μ.real Eforward) := by
  have habs := integral_difference_abs_le_bad_event_mass
    μ F G hF_int hG_int B hB E Eforward hE hEforward hF_bounds hG_bounds h_eq_off_bad
  rcases abs_le.mp habs with ⟨hlo, hhi⟩
  exact ⟨hlo, hhi⟩

/-- Subtracting the two expected rewards from a common comparator preserves
the same exceptional-event error bound.

Source comparison: `sources/zip4/manuscript/08_main_theorem.tex:67-75`. -/
theorem comparator_minus_integral_le_of_bad_event_mass
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F G : Ω → ℝ)
    (hF_int : Integrable F μ) (hG_int : Integrable G μ)
    (B : ℝ) (hB : 0 ≤ B)
    (E Eforward : Set Ω)
    (hE : MeasurableSet E) (hEforward : MeasurableSet Eforward)
    (hF_bounds : ∀ᵐ x ∂μ, F x ∈ Set.Icc (0 : ℝ) B)
    (hG_bounds : ∀ᵐ x ∂μ, G x ∈ Set.Icc (0 : ℝ) B)
    (h_eq_off_bad : ∀ᵐ x ∂μ, x ∉ (E ∪ Eforward) → F x = G x)
    (C : ℝ) :
    C - (∫ x, F x ∂μ) ≤
      C - (∫ x, G x ∂μ) + B * (μ.real E + μ.real Eforward) := by
  have hbounds := integral_difference_bounds_bad_event_mass
    μ F G hF_int hG_int B hB E Eforward hE hEforward hF_bounds hG_bounds h_eq_off_bad
  linarith [hbounds.1]

end Bandits.Support.ExecutionRegretComparison
