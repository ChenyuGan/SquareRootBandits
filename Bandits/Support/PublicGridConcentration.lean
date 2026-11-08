/-
Copyright (c) 2026 Bandits contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ConstructorDimensions
public import Bandits.Support.RealRewardGridCount
public import Bandits.Support.WholeRowHoeffding

import Bandits.Support.FinitePublicationUnion
import Bandits.Support.RewardMatrixCount
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Simultaneous concentration on the real denominator reward grid

This module proves the quantitative whole-row calculation in
`sources/zip4/manuscript/08_main_theorem.tex:26-65`, using the public table
dimensions from `sources/zip4/manuscript/appendix_b_communication.tex:7-15`.
The matrix carrier is the subtype-valued image grid from
`RealRewardGridCount`; its encoding equivalence supplies the finite count.

The concentration theorem takes an arbitrary measurable, independent,
almost-surely bounded row-cost family. It does not establish that the complete
public table supplies such a family, prove row-only dependence for reference
regret and error probability, carry out the private-randomness integration or
good-ID conditioning, bound the row expectation by regret, or couple actual
regret to the published-row average. The separate rounded-local pathwise bridge
is also outside this module.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace Bandits.Support.PublicGridConcentration

open Bandits.Support.ConstructorDimensions
open Bandits.Support.FinitePublicationUnion
open Bandits.Support.RealRewardGridCount
open Bandits.Support.RewardMatrixCount
open Bandits.Support.WholeRowHoeffding

/-- A reward matrix whose entries lie in the actual real image grid at `D p`.
Source: `sources/zip4/manuscript/08_main_theorem.tex:29,55-64`. -/
@[expose] def RealRewardMatrix (p : Parameters) :=
  Fin (p.T) → Fin (p.K) →
    RealRewardGridCount.realRewardGrid (D p) (D_pos p)

/-- The accepted pointwise encoding equivalence into the actual real reward grid. -/
noncomputable def realRewardMatrixEncodingEquiv (p : Parameters) :
    (Fin (p.T) → Fin (p.K) → Fin (D p + 1)) ≃ RealRewardMatrix p :=
  RealRewardGridCount.realRewardMatrixEncodingEquiv (D p) (p.K) (p.T) (D_pos p)

/-- The real-grid matrices are finite, enumerated through the accepted encoding. -/
noncomputable instance realRewardMatrixFintype (p : Parameters) :
    Fintype (RealRewardMatrix p) :=
  Fintype.ofEquiv _ (realRewardMatrixEncodingEquiv p)

/-- The count of real-grid matrices, obtained through the actual encoding equivalence. -/
theorem realRewardMatrix_card (p : Parameters) :
    Fintype.card (RealRewardMatrix p) = (D p + 1) ^ (p.K * p.T) := by
  calc
    Fintype.card (RealRewardMatrix p) =
        Fintype.card (Fin (p.T) → Fin (p.K) → Fin (D p + 1)) :=
      Fintype.card_congr (realRewardMatrixEncodingEquiv p).symm
    _ = (D p + 1) ^ (p.K * p.T) :=
      RewardMatrixCount.rewardMatrixCount (D p) (p.K) (p.T)

/-- The manuscript's source scale `V = m^(3/2) sqrt(KT) b_N`, in its
literal product-of-square-roots form. -/
@[expose] noncomputable def rowConcentrationScale (p : Parameters) : ℝ :=
  (p.m : ℝ) * Real.sqrt (p.m : ℝ) *
    Real.sqrt ((p.K : ℝ) * (p.T : ℝ)) * (b_N p : ℝ)

/-- The source Hoeffding exponent for the complete-row average. -/
@[expose] noncomputable def rowConcentrationExponent (p : Parameters) : ℝ :=
  (M p : ℝ) * rowConcentrationScale p ^ 2 /
    (2 * (p.m : ℝ) ^ 2 * (p.T : ℝ) ^ 2)

/-- The concentration scale is nonnegative. -/
theorem rowConcentrationScale_nonneg (p : Parameters) :
    0 ≤ rowConcentrationScale p := by
  apply mul_nonneg
  · apply mul_nonneg
    · exact mul_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _)
    · exact Real.sqrt_nonneg _
  · exact Nat.cast_nonneg _

/-- The square of the source scale is exactly `m^3 K T b_N^2`. -/
theorem rowConcentrationScale_sq (p : Parameters) :
    rowConcentrationScale p ^ 2 =
      (p.m : ℝ) ^ 3 * (p.K : ℝ) * (p.T : ℝ) * (b_N p : ℝ) ^ 2 := by
  have hm : 0 ≤ (p.m : ℝ) := Nat.cast_nonneg _
  have hkt : 0 ≤ (p.K : ℝ) * (p.T : ℝ) :=
    mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  simp only [rowConcentrationScale, mul_pow, Real.sq_sqrt hm, Real.sq_sqrt hkt]
  ring

theorem rowConcentrationExponent_lower_bound (p : Parameters) :
    4 * ((p.K : ℝ) * (p.T : ℝ)) * (b_N p : ℝ) ≤
      rowConcentrationExponent p := by
  have hm : 0 < (p.m : ℝ) := Nat.cast_pos.mpr (m_pos p)
  have hT : 0 < (p.T : ℝ) := Nat.cast_pos.mpr (T_pos p)
  have hb : 0 < (b_N p : ℝ) := Nat.cast_pos.mpr (b_N_pos p)
  have hden : 0 < 2 * (p.m : ℝ) ^ 2 * (p.T : ℝ) ^ 2 := by positivity
  have hcoef : 0 ≤ rowConcentrationScale p ^ 2 /
      (2 * (p.m : ℝ) ^ 2 * (p.T : ℝ) ^ 2) := by positivity
  have hM := M_real_lower_bound p
  have hmul := mul_le_mul_of_nonneg_right hM hcoef
  have hcalc :
      ((8 : ℝ) * (p.T : ℝ) ^ 2 / ((p.m : ℝ) * (b_N p : ℝ))) *
          (rowConcentrationScale p ^ 2 /
            (2 * (p.m : ℝ) ^ 2 * (p.T : ℝ) ^ 2)) =
        4 * ((p.K : ℝ) * (p.T : ℝ)) * (b_N p : ℝ) := by
    rw [rowConcentrationScale_sq]
    field_simp [ne_of_gt hm, ne_of_gt hT, ne_of_gt hb]
    ring
  calc
    4 * ((p.K : ℝ) * (p.T : ℝ)) * (b_N p : ℝ) =
        ((8 : ℝ) * (p.T : ℝ) ^ 2 / ((p.m : ℝ) * (b_N p : ℝ))) *
          (rowConcentrationScale p ^ 2 /
            (2 * (p.m : ℝ) ^ 2 * (p.T : ℝ) ^ 2)) := hcalc.symm
    _ ≤ (M p : ℝ) * (rowConcentrationScale p ^ 2 /
          (2 * (p.m : ℝ) ^ 2 * (p.T : ℝ) ^ 2)) := hmul
    _ = rowConcentrationExponent p := by
      unfold rowConcentrationExponent
      field_simp [ne_of_gt hden]

/-- The lower bound from the actual row count dominates both logarithmic
terms required for the real-grid union bound. -/
theorem rowConcentrationExponent_dominates_grid_log (p : Parameters) :
    ((p.K : ℝ) * (p.T : ℝ)) * Real.log ((D p : ℝ) + 1) +
        Real.log (2 * (N p : ℝ)) ≤ rowConcentrationExponent p := by
  exact (ConstructorDimensions.whole_row_log_count_bound p).trans
    (rowConcentrationExponent_lower_bound p)

/-- The complete source exponent chain: the logarithm of the real-grid count
plus `log (2N)` is bounded by `4KTb_N`, which is bounded by the actual
`M V^2/(2m^2T^2)`. -/
theorem rowConcentrationExponent_bounds (p : Parameters) :
    (((p.K : ℝ) * (p.T : ℝ)) * Real.log ((D p : ℝ) + 1) +
        Real.log (2 * (N p : ℝ)) ≤
      4 * ((p.K : ℝ) * (p.T : ℝ)) * (b_N p : ℝ)) ∧
    (4 * ((p.K : ℝ) * (p.T : ℝ)) * (b_N p : ℝ) ≤
      rowConcentrationExponent p) := by
  exact ⟨ConstructorDimensions.whole_row_log_count_bound p,
    rowConcentrationExponent_lower_bound p⟩

/-- For every real-grid matrix, the bad event in the simultaneous estimate. -/
@[expose] def rowConcentrationBadEvent {Ω : Type*} [MeasurableSpace Ω]
    (p : Parameters) (μ : Measure Ω)
    (G : RealRewardMatrix p → Fin (M p) → Ω → ℝ)
    (r : RealRewardMatrix p) : Set Ω :=
  {ω | WholeRowHoeffding.muG μ (G r) + 2 * rowConcentrationScale p <
    WholeRowHoeffding.barG (G r) ω}

/-- The literal simultaneous event over every real denominator-`D` matrix. -/
@[expose] noncomputable def rowConcentrationGoodEvent {Ω : Type*}
    [MeasurableSpace Ω] (p : Parameters) (μ : Measure Ω)
    (G : RealRewardMatrix p → Fin (M p) → Ω → ℝ) : Set Ω :=
  {ω | ∀ r : RealRewardMatrix p,
    WholeRowHoeffding.barG (G r) ω ≤
      WholeRowHoeffding.muG μ (G r) + 2 * rowConcentrationScale p}

/-- The complement of the simultaneous good event is the union of the
single-matrix Hoeffding bad events. -/
theorem rowConcentrationGoodEvent_compl_eq_iUnion {Ω : Type*}
    [MeasurableSpace Ω] (p : Parameters) (μ : Measure Ω)
    (G : RealRewardMatrix p → Fin (M p) → Ω → ℝ) :
    (rowConcentrationGoodEvent p μ G)ᶜ =
      ⋃ r : RealRewardMatrix p, rowConcentrationBadEvent p μ G r := by
  ext ω
  simp [rowConcentrationGoodEvent, rowConcentrationBadEvent]

/-- Measurability of the literal simultaneous event from pointwise measurable
row costs. -/
theorem measurableSet_rowConcentrationGoodEvent {Ω : Type*}
    [MeasurableSpace Ω] (p : Parameters) (μ : Measure Ω)
    (G : RealRewardMatrix p → Fin (M p) → Ω → ℝ)
    (h_meas : ∀ r j, Measurable (G r j)) :
    MeasurableSet (rowConcentrationGoodEvent p μ G) := by
  classical
  rw [rowConcentrationGoodEvent, Set.ofPred_forall]
  exact MeasurableSet.iInter fun r => by
    have hbar : Measurable (WholeRowHoeffding.barG (G r)) := by
      unfold WholeRowHoeffding.barG
      fun_prop
    exact measurableSet_le hbar measurable_const

private theorem rowConcentrationBadEvent_measure_le_exp {Ω : Type*}
    [MeasurableSpace Ω] (p : Parameters) (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (G : RealRewardMatrix p → Fin (M p) → Ω → ℝ)
    (r : RealRewardMatrix p)
    (h_indep : ∀ r, ProbabilityTheory.iIndepFun (G r) μ)
    (h_meas : ∀ r j, Measurable (G r j))
    (h_bounds : ∀ r j, ∀ᵐ ω ∂μ,
      G r j ω ∈ Set.Icc (-(p.m : ℝ) * (p.T : ℝ))
        (3 * (p.m : ℝ) * (p.T : ℝ))) :
    μ (rowConcentrationBadEvent p μ G r) ≤
      ENNReal.ofReal (Real.exp (-rowConcentrationExponent p)) := by
  have htail := WholeRowHoeffding.wholeRowHoeffding
    (hM := M_pos p) (hm := m_pos p) (hT := T_pos p) (μ := μ) (G := G r)
    (h_indep r) (fun j => (h_meas r j).aemeasurable)
    (fun j => h_bounds r j) (rowConcentrationScale_nonneg p)
  have hexp_eq :
      -((M p : ℝ) * rowConcentrationScale p ^ 2) /
          (2 * (p.m : ℝ) ^ 2 * (p.T : ℝ) ^ 2) =
        -rowConcentrationExponent p := by
    unfold rowConcentrationExponent
    ring
  rw [hexp_eq] at htail
  have htail' :
      μ.real (rowConcentrationBadEvent p μ G r) ≤
        Real.exp (-rowConcentrationExponent p) := by
    simpa [rowConcentrationBadEvent, rowConcentrationExponent] using htail
  have hmeasure_le_one : μ (rowConcentrationBadEvent p μ G r) ≤ 1 := by
    calc
      μ (rowConcentrationBadEvent p μ G r) ≤ μ Set.univ :=
        measure_mono (Set.subset_univ _)
      _ = 1 := by simp
  have hfinite : μ (rowConcentrationBadEvent p μ G r) ≠ ∞ :=
    ne_of_lt (lt_of_le_of_lt hmeasure_le_one ENNReal.one_lt_top)
  rw [← ENNReal.ofReal_toReal hfinite]
  exact ENNReal.ofReal_le_ofReal htail'

private theorem scaled_exp_le_reciprocal (p : Parameters) :
    (Fintype.card (RealRewardMatrix p) : ℝ) *
        Real.exp (-rowConcentrationExponent p) ≤
      1 / (2 * (N p : ℝ)) := by
  let q : ℝ := (D p : ℝ) + 1
  let z : ℝ := 2 * (N p : ℝ)
  have hq : 0 < q := by dsimp [q]; positivity
  have hz : 0 < z := by
    dsimp [z]
    exact mul_pos (by norm_num) (Nat.cast_pos.mpr (N_pos p))
  have hn_cast : ((p.K * p.T : ℕ) : ℝ) = (p.K : ℝ) * (p.T : ℝ) := by
    simp
  have hpow :
      Real.exp (((p.K * p.T : ℕ) : ℝ) * Real.log q) = q ^ (p.K * p.T) := by
    rw [← Real.log_pow q (p.K * p.T), Real.exp_log (pow_pos hq _)]
  have h_exp_eq :
      Real.exp (-(((p.K : ℝ) * (p.T : ℝ)) * Real.log q + Real.log z)) =
        1 / (q ^ (p.K * p.T) * z) := by
    calc
      Real.exp (-(((p.K : ℝ) * (p.T : ℝ)) * Real.log q + Real.log z)) =
          Real.exp (-(((p.K * p.T : ℕ) : ℝ) * Real.log q)) *
            Real.exp (-Real.log z) := by rw [← hn_cast, neg_add, Real.exp_add]
      _ = (q ^ (p.K * p.T))⁻¹ * z⁻¹ := by
        rw [Real.exp_neg, hpow, Real.exp_neg, Real.exp_log hz]
      _ = 1 / (q ^ (p.K * p.T) * z) := by ring
  have hlog := rowConcentrationExponent_dominates_grid_log p
  have h_exp_bound :
      Real.exp (-rowConcentrationExponent p) ≤
        1 / (q ^ (p.K * p.T) * z) := by
    have hmono := Real.exp_le_exp.mpr (neg_le_neg hlog)
    have hqz :
        Real.exp (-(((p.K : ℝ) * (p.T : ℝ)) * Real.log q + Real.log z)) =
          1 / (q ^ (p.K * p.T) * z) := by
      simpa [q, z] using h_exp_eq
    exact hmono.trans_eq hqz
  have hcard :
      (Fintype.card (RealRewardMatrix p) : ℝ) = q ^ (p.K * p.T) := by
    rw [realRewardMatrix_card]
    simp [q, Nat.cast_pow, Nat.cast_add]
  rw [hcard]
  calc
    q ^ (p.K * p.T) * Real.exp (-rowConcentrationExponent p) ≤
        q ^ (p.K * p.T) * (1 / (q ^ (p.K * p.T) * z)) :=
      mul_le_mul_of_nonneg_left h_exp_bound (pow_nonneg hq.le _)
    _ = 1 / (2 * (N p : ℝ)) := by
      dsimp [z]
      field_simp [ne_of_gt (pow_pos hq _), ne_of_gt hz]

private theorem scaled_exp_le_ennreal_reciprocal (p : Parameters) :
    (Fintype.card (RealRewardMatrix p) : ℝ≥0∞) *
        ENNReal.ofReal (Real.exp (-rowConcentrationExponent p)) ≤
      ENNReal.ofReal (1 / (2 * (N p : ℝ))) := by
  have hreal := scaled_exp_le_reciprocal p
  have hexp : 0 ≤ Real.exp (-rowConcentrationExponent p) :=
    le_of_lt (Real.exp_pos _)
  calc
    (Fintype.card (RealRewardMatrix p) : ℝ≥0∞) *
        ENNReal.ofReal (Real.exp (-rowConcentrationExponent p)) =
      ENNReal.ofReal ((Fintype.card (RealRewardMatrix p) : ℝ) *
        Real.exp (-rowConcentrationExponent p)) := by
          rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul' hexp]
    _ ≤ ENNReal.ofReal (1 / (2 * (N p : ℝ))) :=
      ENNReal.ofReal_le_ofReal hreal

/-- The simultaneous bad-event probability is at most the source's stronger
`1/(2N)` bound. Independence is required only among rows for each fixed matrix;
there is no cross-matrix independence or identical-distribution premise. -/
theorem rowConcentrationGoodEvent_failure_prob_le {Ω : Type*}
    [MeasurableSpace Ω] (p : Parameters) (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (G : RealRewardMatrix p → Fin (M p) → Ω → ℝ)
    (h_indep : ∀ r, ProbabilityTheory.iIndepFun (G r) μ)
    (h_meas : ∀ r j, Measurable (G r j))
    (h_bounds : ∀ r j, ∀ᵐ ω ∂μ,
      G r j ω ∈ Set.Icc (-(p.m : ℝ) * (p.T : ℝ))
        (3 * (p.m : ℝ) * (p.T : ℝ))) :
    μ.real (rowConcentrationGoodEvent p μ G)ᶜ ≤ 1 / (2 * (N p : ℝ)) := by
  classical
  have hsingle : ∀ r : RealRewardMatrix p,
      μ (rowConcentrationBadEvent p μ G r) ≤
        ENNReal.ofReal (Real.exp (-rowConcentrationExponent p)) := by
    intro r
    exact rowConcentrationBadEvent_measure_le_exp p μ G r h_indep h_meas h_bounds
  have hunion := FinitePublicationUnion.finiteTypeUnionBound μ
    (rowConcentrationBadEvent p μ G)
    (ENNReal.ofReal (Real.exp (-rowConcentrationExponent p))) hsingle
  have hunion' :
      μ (⋃ r : RealRewardMatrix p, rowConcentrationBadEvent p μ G r) ≤
        ENNReal.ofReal (1 / (2 * (N p : ℝ))) :=
    hunion.trans (scaled_exp_le_ennreal_reciprocal p)
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hunion'
  rw [rowConcentrationGoodEvent_compl_eq_iUnion]
  simpa [MeasureTheory.measureReal_def, show 0 ≤ 1 / (2 * (N p : ℝ)) by positivity]
    using hreal

/-- The simultaneous failure probability is also bounded by `1/N`. -/
theorem rowConcentrationGoodEvent_failure_prob_le_one_div_N {Ω : Type*}
    [MeasurableSpace Ω] (p : Parameters) (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (G : RealRewardMatrix p → Fin (M p) → Ω → ℝ)
    (h_indep : ∀ r, ProbabilityTheory.iIndepFun (G r) μ)
    (h_meas : ∀ r j, Measurable (G r j))
    (h_bounds : ∀ r j, ∀ᵐ ω ∂μ,
      G r j ω ∈ Set.Icc (-(p.m : ℝ) * (p.T : ℝ))
        (3 * (p.m : ℝ) * (p.T : ℝ))) :
    μ.real (rowConcentrationGoodEvent p μ G)ᶜ ≤ 1 / (N p : ℝ) := by
  have hhalf := rowConcentrationGoodEvent_failure_prob_le
    p μ G h_indep h_meas h_bounds
  have hN : 0 < (N p : ℝ) := Nat.cast_pos.mpr (N_pos p)
  have hden : 0 < 2 * (N p : ℝ) := by positivity
  have hfrac : (1 : ℝ) / (2 * (N p : ℝ)) ≤ 1 / (N p : ℝ) := by
    rw [div_le_div_iff₀ hden hN]
    nlinarith
  exact hhalf.trans hfrac

/-- The literal good event has probability at least `1 - 1/N`. -/
theorem rowConcentrationGoodEvent_prob_ge {Ω : Type*}
    [MeasurableSpace Ω] (p : Parameters) (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (G : RealRewardMatrix p → Fin (M p) → Ω → ℝ)
    (h_indep : ∀ r, ProbabilityTheory.iIndepFun (G r) μ)
    (h_meas : ∀ r j, Measurable (G r j))
    (h_bounds : ∀ r j, ∀ᵐ ω ∂μ,
      G r j ω ∈ Set.Icc (-(p.m : ℝ) * (p.T : ℝ))
        (3 * (p.m : ℝ) * (p.T : ℝ))) :
    1 - 1 / (N p : ℝ) ≤ μ.real (rowConcentrationGoodEvent p μ G) := by
  have hfail := rowConcentrationGoodEvent_failure_prob_le_one_div_N
    p μ G h_indep h_meas h_bounds
  have hmeas := measurableSet_rowConcentrationGoodEvent p μ G h_meas
  have hcompl :
      μ.real (rowConcentrationGoodEvent p μ G)ᶜ =
        1 - μ.real (rowConcentrationGoodEvent p μ G) := by
    simpa using MeasureTheory.measureReal_compl (μ := μ) hmeas
  linarith

end Bandits.Support.PublicGridConcentration

end
