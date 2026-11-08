/-
Copyright (c) 2026 Bandits Lean preparation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.PhaseStartConditionalWaiting

import Mathlib.Analysis.Convex.Integral
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Phase-start waiting from an inclusive terminal service count

These internal extensions use the actual terminal count `N P X i T ω ≤ q`.
The existing task-level localized exponential supermartingale argument then
gives the same phase-start bounds without inferring any strict pre-round quota.
Physical producers must provide the displayed count, stopping, support,
predictability, nesting, and conditional-service inputs.

The source is `sources/zip4/manuscript/05_binary_transport.tex:180-240` and
`sources/zip4/manuscript/06_interruptions.tex:476-481`.
-/

@[expose] public section

namespace Bandits.Support.PhaseStartInclusiveCountWaiting

open MeasureTheory
open scoped BigOperators MeasureTheory Convex ENNReal

open Bandits.Support.PhaseServiceWaiting
open Bandits.Support.PhaseStartConditionalWaiting

/-- Localized task exponential moment from the actual inclusive terminal
service count. The localized `Z` estimate and `N(T) ≤ q` give the pointwise
comparison with the exact factor `exp(q)`. -/
theorem localized_task_exponential_bound_of_terminalCount
    {Ω : Type*} [MeasurableSpace Ω] {m : MeasurableSpace Ω}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {d T K q : ℕ} (ℱ : MeasureTheory.Filtration ℕ m)
    (P : ℕ → Ω → Finset (Fin d)) (X : Fin d → ℕ → Ω → Bool)
    (w : ℕ → Ω → ℝ) (sigma theta : Ω → ℕ) (a : ℝ) (ha : 0 < a)
    (hsigma : IsPreRoundStoppingTime ℱ sigma)
    (hP : ∀ i t, t < T →
      MeasurableSet[ℱ (t + 1)] {ω | i ∈ P t ω})
    (hphase : ∀ t, t < T → ∀ ω, (P t ω).Nonempty →
      sigma ω ≤ t + 1 ∧ t + 1 < theta ω)
    (hw_meas : ∀ t, t < T →
      StronglyMeasurable[ℱ (t + 1)] (w t))
    (hw_bound : ∀ t, t < T → ∀ ω,
      w t ω ∈ Set.Icc (0 : ℝ) (K : ℝ))
    (hX_meas : ∀ i t, t < T →
      StronglyMeasurable[ℱ (t + 2)] (observation X i t))
    (hterminalCount : ∀ (i : Fin d) ω, N P X i T ω ≤ q)
    (hservice : ∀ i t, t < T → ∀ᵐ ω ∂μ, i ∈ P t ω →
      a * w t ω ≤ μ[observation X i t | ℱ (t + 1)] ω)
    (B : Set Ω) (hB : MeasurableSet[phaseStartSigmaAlgebra ℱ sigma hsigma] B)
    (i : Fin d) :
    ∫ ω in B, Real.exp (kappa * a * G P w i T ω) ∂μ ≤
      Real.exp (q : ℝ) * μ.real B := by
  have hZbound := localized_Z_integral_bound μ ℱ P X w sigma theta a ha hsigma
    hP hphase hw_meas hw_bound hX_meas hservice B hB i
  have hZint := Z_integrable μ ℱ P X w a ha hP hw_meas hw_bound hX_meas
    i T le_rfl
  have hExpInt := task_charge_exponential_integrable μ ℱ P w a ha
    hP hw_meas hw_bound i
  have hNle : ∀ ω, N P X i T ω ≤ q := by
    intro ω
    exact hterminalCount i ω
  have hpoint : ∀ ω,
      Real.exp (kappa * a * G P w i T ω) ≤
        Real.exp (q : ℝ) * Z P X w a i T ω := by
    intro ω
    have hEq : Real.exp (kappa * a * G P w i T ω) =
        Z P X w a i T ω * Real.exp (N P X i T ω : ℝ) := by
      calc
        Real.exp (kappa * a * G P w i T ω) =
            Real.exp ((kappa * a * G P w i T ω - (N P X i T ω : ℝ)) +
              (N P X i T ω : ℝ)) := by congr 1; ring
        _ = Real.exp (kappa * a * G P w i T ω -
              (N P X i T ω : ℝ)) * Real.exp (N P X i T ω : ℝ) :=
          Real.exp_add _ _
        _ = Z P X w a i T ω * Real.exp (N P X i T ω : ℝ) := by rw [Z]
    rw [hEq]
    have hNat : (N P X i T ω : ℝ) ≤ (q : ℝ) := by exact_mod_cast hNle ω
    calc
      Z P X w a i T ω * Real.exp (N P X i T ω : ℝ) ≤
          Z P X w a i T ω * Real.exp (q : ℝ) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hNat) (Real.exp_pos _).le
      _ = Real.exp (q : ℝ) * Z P X w a i T ω := mul_comm _ _
  calc
    ∫ ω in B, Real.exp (kappa * a * G P w i T ω) ∂μ ≤
        ∫ ω in B, Real.exp (q : ℝ) * Z P X w a i T ω ∂μ :=
      setIntegral_mono_ae hExpInt.integrableOn (hZint.const_mul _).integrableOn
        (ae_of_all μ hpoint)
    _ = Real.exp (q : ℝ) * ∫ ω in B, Z P X w a i T ω ∂μ := by
      rw [integral_const_mul]
    _ ≤ Real.exp (q : ℝ) * μ.real B :=
      mul_le_mul_of_nonneg_left hZbound (Real.exp_pos _).le

/-- The localized total-charge exponential moment, obtained from the original
task family and the same pathwise maximum-of-task-charges identity. -/
theorem phase_start_totalCharge_exponential_setIntegral_bound_of_terminalCount
    {Ω : Type*} [MeasurableSpace Ω] {m : MeasurableSpace Ω}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {d T K q : ℕ} (hd : 0 < d) (_hT : 0 < T) (_hK : 0 < K) (_hq : 0 < q)
    (ℱ : MeasureTheory.Filtration ℕ m)
    (P : ℕ → Ω → Finset (Fin d)) (X : Fin d → ℕ → Ω → Bool)
    (w : ℕ → Ω → ℝ) (sigma theta : Ω → ℕ) (a : ℝ) (ha : 0 < a)
    (hsigma : IsPreRoundStoppingTime ℱ sigma)
    (htheta : IsPreRoundStoppingTime ℱ theta)
    (_hsigma_start : ∀ ω, 1 ≤ sigma ω)
    (_hsigma_le_theta : ∀ ω, sigma ω ≤ theta ω)
    (_htheta_bound : ∀ ω, theta ω ≤ T + 1)
    (hP : ∀ i t, t < T →
      MeasurableSet[ℱ (t + 1)] {ω | i ∈ P t ω})
    (hphase : ∀ t, t < T → ∀ ω, (P t ω).Nonempty →
      sigma ω ≤ t + 1 ∧ t + 1 < theta ω)
    (hnested : ∀ s t, s ≤ t → t < T → ∀ ω,
      sigma ω ≤ s + 1 → t + 1 < theta ω → P t ω ⊆ P s ω)
    (hw_meas : ∀ t, t < T →
      StronglyMeasurable[ℱ (t + 1)] (w t))
    (hw_bound : ∀ t, t < T → ∀ ω,
      w t ω ∈ Set.Icc (0 : ℝ) (K : ℝ))
    (hX_meas : ∀ i t, t < T →
      StronglyMeasurable[ℱ (t + 2)] (observation X i t))
    (hterminalCount : ∀ (i : Fin d) ω, N P X i T ω ≤ q)
    (hservice : ∀ i t, t < T → ∀ᵐ ω ∂μ, i ∈ P t ω →
      a * w t ω ≤ μ[observation X i t | ℱ (t + 1)] ω)
    (B : Set Ω) (hB : MeasurableSet[phaseStartSigmaAlgebra ℱ sigma hsigma] B) :
    ∫ ω in B, Real.exp (kappa * a * totalCharge P sigma theta w T ω) ∂μ ≤
      (d : ℝ) * Real.exp (q : ℝ) * μ.real B := by
  have htotalInt := totalCharge_exp_integrable μ ℱ P sigma theta w a ha
    hsigma htheta hP hw_meas hphase hw_bound
  have htaskInt : ∀ i : Fin d,
      Integrable (fun ω => Real.exp (kappa * a * G P w i T ω)) μ := by
    intro i
    exact task_charge_exponential_integrable μ ℱ P w a ha hP hw_meas
      hw_bound i
  have hsumInt :
      Integrable (fun ω => ∑ i ∈ Finset.univ,
        Real.exp (kappa * a * G P w i T ω)) μ := by
    apply integrable_finsetSum
    intro i hi
    exact htaskInt i
  have hpoint : ∀ ω,
      Real.exp (kappa * a * totalCharge P sigma theta w T ω) ≤
        ∑ i ∈ Finset.univ, Real.exp (kappa * a * G P w i T ω) := by
    intro ω
    have hmax := totalCharge_eq_maxTaskCharge hd P sigma theta w
      hphase hnested (fun t ht ω => (hw_bound t ht ω).1) ω
    have hFinNonempty : (Finset.univ : Finset (Fin d)).Nonempty :=
      Finset.univ_nonempty_iff.mpr ⟨⟨0, hd⟩⟩
    obtain ⟨i, hi, hsup⟩ :=
      Finset.exists_mem_eq_sup' hFinNonempty (fun i => G P w i T ω)
    rw [hmax]
    change Real.exp (kappa * a *
      Finset.univ.sup' hFinNonempty (fun j => G P w j T ω)) ≤ _
    rw [hsup]
    exact Finset.single_le_sum
      (f := fun j : Fin d => Real.exp (kappa * a * G P w j T ω))
      (fun j hj => (Real.exp_pos _).le) hi
  have hsumSet :
      ∫ ω in B, (∑ i ∈ Finset.univ,
        Real.exp (kappa * a * G P w i T ω)) ∂μ =
        ∑ i ∈ Finset.univ,
          ∫ ω in B, Real.exp (kappa * a * G P w i T ω) ∂μ := by
    rw [integral_finsetSum]
    intro i hi
    exact (htaskInt i).integrableOn
  calc
    ∫ ω in B, Real.exp (kappa * a * totalCharge P sigma theta w T ω) ∂μ ≤
        ∫ ω in B, (∑ i ∈ Finset.univ,
          Real.exp (kappa * a * G P w i T ω)) ∂μ :=
      setIntegral_mono_ae htotalInt.2.integrableOn hsumInt.integrableOn
        (ae_of_all μ hpoint)
    _ = ∑ i ∈ Finset.univ,
        ∫ ω in B, Real.exp (kappa * a * G P w i T ω) ∂μ := hsumSet
    _ ≤ ∑ i ∈ Finset.univ,
        Real.exp (q : ℝ) * μ.real B := by
      apply Finset.sum_le_sum
      intro i hi
      exact localized_task_exponential_bound_of_terminalCount μ ℱ P X w
        sigma theta a ha hsigma hP hphase hw_meas hw_bound hX_meas
        hterminalCount hservice B hB i
    _ = (d : ℝ) * Real.exp (q : ℝ) * μ.real B := by simp [mul_assoc]

/-- The localized total-charge bound from restricted-set Jensen, retaining the
exact mass of every measurable phase-start set, including null sets. -/
theorem phase_start_totalCharge_setIntegral_bound_of_terminalCount
    {Ω : Type*} [MeasurableSpace Ω] {m : MeasurableSpace Ω}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {d T K q : ℕ} (hd : 0 < d) (_hT : 0 < T) (_hK : 0 < K) (_hq : 0 < q)
    (ℱ : MeasureTheory.Filtration ℕ m)
    (P : ℕ → Ω → Finset (Fin d)) (X : Fin d → ℕ → Ω → Bool)
    (w : ℕ → Ω → ℝ) (sigma theta : Ω → ℕ) (a : ℝ) (ha : 0 < a)
    (hsigma : IsPreRoundStoppingTime ℱ sigma)
    (htheta : IsPreRoundStoppingTime ℱ theta)
    (_hsigma_start : ∀ ω, 1 ≤ sigma ω)
    (_hsigma_le_theta : ∀ ω, sigma ω ≤ theta ω)
    (_htheta_bound : ∀ ω, theta ω ≤ T + 1)
    (hP : ∀ i t, t < T →
      MeasurableSet[ℱ (t + 1)] {ω | i ∈ P t ω})
    (hphase : ∀ t, t < T → ∀ ω, (P t ω).Nonempty →
      sigma ω ≤ t + 1 ∧ t + 1 < theta ω)
    (hnested : ∀ s t, s ≤ t → t < T → ∀ ω,
      sigma ω ≤ s + 1 → t + 1 < theta ω → P t ω ⊆ P s ω)
    (hw_meas : ∀ t, t < T →
      StronglyMeasurable[ℱ (t + 1)] (w t))
    (hw_bound : ∀ t, t < T → ∀ ω,
      w t ω ∈ Set.Icc (0 : ℝ) (K : ℝ))
    (hX_meas : ∀ i t, t < T →
      StronglyMeasurable[ℱ (t + 2)] (observation X i t))
    (hterminalCount : ∀ (i : Fin d) ω, N P X i T ω ≤ q)
    (hservice : ∀ i t, t < T → ∀ᵐ ω ∂μ, i ∈ P t ω →
      a * w t ω ≤ μ[observation X i t | ℱ (t + 1)] ω)
    (B : Set Ω) (hB : MeasurableSet[phaseStartSigmaAlgebra ℱ sigma hsigma] B) :
    ∫ ω in B, totalCharge P sigma theta w T ω ∂μ ≤
      (((q : ℝ) + Real.log (d : ℝ)) / (kappa * a)) * μ.real B := by
  have htotalInt := totalCharge_exp_integrable μ ℱ P sigma theta w a ha
    hsigma htheta hP hw_meas hphase hw_bound
  have hcpos : 0 < kappa * a := mul_pos kappa_pos ha
  by_cases hBzero : μ B = 0
  · have hBreal : μ.real B = 0 := by simp [measureReal_def, hBzero]
    have hrestrict : μ.restrict B = 0 := Measure.restrict_eq_zero.2 hBzero
    change ∫ ω, totalCharge P sigma theta w T ω ∂μ.restrict B ≤ _
    rw [hrestrict, integral_zero_measure]
    simp [hBreal]
  · have hBfinite : μ B ≠ ∞ := measure_ne_top μ B
    have hBrealPos : 0 < μ.real B := ENNReal.toReal_pos hBzero hBfinite
    let c : ℝ := kappa * a
    have hconvex : ConvexOn ℝ Set.univ
        (fun x : ℝ => Real.exp (c * x)) := by
      convert! convexOn_exp.comp_linearMap (LinearMap.mul ℝ ℝ c) using 1
    have hJensen :
        Real.exp (c * (⨍ ω in B, totalCharge P sigma theta w T ω ∂μ)) ≤
          ⨍ ω in B,
            Real.exp (c * totalCharge P sigma theta w T ω) ∂μ := by
      simpa [Function.comp_def, c] using
        hconvex.map_set_average_le
          (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn
          isClosed_univ hBzero hBfinite
          (ae_of_all (μ.restrict B) fun _ => Set.mem_univ _)
          htotalInt.1.integrableOn htotalInt.2.integrableOn
    have hExpSet :=
      phase_start_totalCharge_exponential_setIntegral_bound_of_terminalCount
        μ hd _hT _hK _hq ℱ P X w sigma theta a ha hsigma htheta
        _hsigma_start _hsigma_le_theta _htheta_bound hP hphase hnested
        hw_meas hw_bound hX_meas hterminalCount hservice B hB
    have hAvgExp :
        (⨍ ω in B,
          Real.exp (c * totalCharge P sigma theta w T ω) ∂μ) ≤
          (d : ℝ) * Real.exp (q : ℝ) := by
      rw [setAverage_eq]
      calc
        (μ.real B)⁻¹ * ∫ ω in B,
            Real.exp (c * totalCharge P sigma theta w T ω) ∂μ ≤
          (μ.real B)⁻¹ *
            ((d : ℝ) * Real.exp (q : ℝ) * μ.real B) :=
          mul_le_mul_of_nonneg_left hExpSet (inv_nonneg.mpr hBrealPos.le)
        _ = (d : ℝ) * Real.exp (q : ℝ) := by
          field_simp [ne_of_gt hBrealPos]
    have hmeanExp :
        Real.exp (c * (⨍ ω in B, totalCharge P sigma theta w T ω ∂μ)) ≤
          Real.exp (Real.log (d : ℝ) + (q : ℝ)) := by
      calc
        Real.exp (c * (⨍ ω in B, totalCharge P sigma theta w T ω ∂μ)) ≤
            ⨍ ω in B,
              Real.exp (c * totalCharge P sigma theta w T ω) ∂μ := hJensen
        _ ≤ (d : ℝ) * Real.exp (q : ℝ) := hAvgExp
        _ = Real.exp (Real.log (d : ℝ) + (q : ℝ)) := by
          rw [Real.exp_add]
          congr 1
          exact (Real.exp_log (Nat.cast_pos.mpr hd)).symm
    have hmean := Real.exp_le_exp.mp hmeanExp
    have havgIntegral := measure_smul_setAverage
      (fun ω => totalCharge P sigma theta w T ω) hBfinite
    have hscaled :
        c * (∫ ω in B, totalCharge P sigma theta w T ω ∂μ) ≤
          ((q : ℝ) + Real.log (d : ℝ)) * μ.real B := by
      calc
        c * (∫ ω in B, totalCharge P sigma theta w T ω ∂μ) =
            μ.real B * (c * (⨍ ω in B,
              totalCharge P sigma theta w T ω ∂μ)) := by
          rw [← havgIntegral]
          simp only [smul_eq_mul]
          ring
        _ ≤ μ.real B * ((q : ℝ) + Real.log (d : ℝ)) :=
          mul_le_mul_of_nonneg_left (by nlinarith [hmean])
            (measureReal_nonneg)
        _ = ((q : ℝ) + Real.log (d : ℝ)) * μ.real B := mul_comm _ _
    calc
      ∫ ω in B, totalCharge P sigma theta w T ω ∂μ =
          c⁻¹ * (c * ∫ ω in B, totalCharge P sigma theta w T ω ∂μ) := by
        rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hcpos), one_mul]
      _ ≤ c⁻¹ * (((q : ℝ) + Real.log (d : ℝ)) * μ.real B) :=
        mul_le_mul_of_nonneg_left hscaled (inv_nonneg.mpr hcpos.le)
      _ = (((q : ℝ) + Real.log (d : ℝ)) / c) * μ.real B := by
        rw [div_eq_mul_inv]
        ring

/-- The total phase waiting bound as an almost-everywhere conditional
expectation inequality under the actual Mathlib phase-start σ-algebra. -/
theorem phase_start_totalCharge_condExp_bound_of_terminalCount
    {Ω : Type*} [MeasurableSpace Ω] {m : MeasurableSpace Ω}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {d T K q : ℕ} (hd : 0 < d) (_hT : 0 < T) (_hK : 0 < K) (_hq : 0 < q)
    (ℱ : MeasureTheory.Filtration ℕ m)
    (P : ℕ → Ω → Finset (Fin d)) (X : Fin d → ℕ → Ω → Bool)
    (w : ℕ → Ω → ℝ) (sigma theta : Ω → ℕ) (a : ℝ) (ha : 0 < a)
    (hsigma : IsPreRoundStoppingTime ℱ sigma)
    (htheta : IsPreRoundStoppingTime ℱ theta)
    (_hsigma_start : ∀ ω, 1 ≤ sigma ω)
    (_hsigma_le_theta : ∀ ω, sigma ω ≤ theta ω)
    (_htheta_bound : ∀ ω, theta ω ≤ T + 1)
    (hP : ∀ i t, t < T →
      MeasurableSet[ℱ (t + 1)] {ω | i ∈ P t ω})
    (hphase : ∀ t, t < T → ∀ ω, (P t ω).Nonempty →
      sigma ω ≤ t + 1 ∧ t + 1 < theta ω)
    (hnested : ∀ s t, s ≤ t → t < T → ∀ ω,
      sigma ω ≤ s + 1 → t + 1 < theta ω → P t ω ⊆ P s ω)
    (hw_meas : ∀ t, t < T →
      StronglyMeasurable[ℱ (t + 1)] (w t))
    (hw_bound : ∀ t, t < T → ∀ ω,
      w t ω ∈ Set.Icc (0 : ℝ) (K : ℝ))
    (hX_meas : ∀ i t, t < T →
      StronglyMeasurable[ℱ (t + 2)] (observation X i t))
    (hterminalCount : ∀ (i : Fin d) ω, N P X i T ω ≤ q)
    (hservice : ∀ i t, t < T → ∀ᵐ ω ∂μ, i ∈ P t ω →
      a * w t ω ≤ μ[observation X i t | ℱ (t + 1)] ω) :
    μ[totalCharge P sigma theta w T | phaseStartSigmaAlgebra ℱ sigma hsigma]
      ≤ᵐ[μ] fun _ =>
        ((q : ℝ) + Real.log (d : ℝ)) / (kappa * a) := by
  let mσ := phaseStartSigmaAlgebra ℱ sigma hsigma
  have hmσ : mσ ≤ m := phaseStartSigmaAlgebra_le ℱ sigma hsigma
  have htotalInt := totalCharge_exp_integrable μ ℱ P sigma theta w a ha
    hsigma htheta hP hw_meas hphase hw_bound
  have hset : ∀ B, MeasurableSet[mσ] B →
      ∫ ω in B, totalCharge P sigma theta w T ω ∂μ ≤
        (((q : ℝ) + Real.log (d : ℝ)) / (kappa * a)) * μ.real B := by
    intro B hB
    exact phase_start_totalCharge_setIntegral_bound_of_terminalCount
      μ hd _hT _hK _hq ℱ P X w sigma theta a ha hsigma htheta
      _hsigma_start _hsigma_le_theta _htheta_bound hP hphase hnested
      hw_meas hw_bound hX_meas hterminalCount hservice B hB
  exact (setIntegral_iff_condExp_le μ mσ hmσ
    (totalCharge P sigma theta w T)
    (((q : ℝ) + Real.log (d : ℝ)) / (kappa * a)) htotalInt.1).mp hset

end Bandits.Support.PhaseStartInclusiveCountWaiting

end
