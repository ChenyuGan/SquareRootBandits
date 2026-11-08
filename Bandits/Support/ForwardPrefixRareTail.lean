/-
Copyright (c) 2026 Bandits Lean regret formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ConstructorDimensions
public import Bandits.Support.BootstrapDimensions
public import Bandits.Support.ForwardPrefixSlice

import Bandits.Support.FalseForwardContextUnion
import Bandits.Support.RareTailBound
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Fixed-context rare-tail bound for false forward prefixes

For each fixed private eligibility function, the integrated passing weights
over false-row and identification-index slices obey the rare-tail estimate.
The statement is only for one fixed block, true index, private probability
space, and labelwise eligibility family.

Sources: `sources/zip4/manuscript/appendix_b_communication.tex:316-350`
and `sources/zip4/manuscript/07_public_setup.tex:15-25`.
-/

public section

open MeasureTheory
open ProbabilityTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.ForwardPrefixSlice
open Bandits.Support.CompletePublicTable
open scoped BigOperators

namespace Bandits.Support.ForwardPrefixRareTail

/-- The local threshold `1 / (B_boot * n_boot)` from the communication lemma. -/
@[expose] noncomputable def localEpsilon (p : Parameters) : ℝ :=
  1 / ((B_boot p : ℝ) * (n_boot p : ℝ))

/-- The source rare-tail mean parameter `N^3 * exp(-8 b_N)`. -/
@[expose] noncomputable def localRareTailNu (p : Parameters) : ℝ :=
  (N p : ℝ) ^ 3 * Real.exp (-8 * (b_N p : ℝ))

/-- The integrated private passing weight for one full-family slice, with the
true row set to zero. This extension retains independence on the full
`ForwardFamily` even when there are no false rows. -/
@[expose] noncomputable def zeroedIntegratedPrivatePassing
    {p : Parameters} {s : Fin (n_boot p)} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (E : SliceLabel p → EligibleListFunction p s Ω) (J : Fin (M p))
    (label : SliceLabel p) (x : ForwardFamily p) : ℝ :=
  if label.1 = J then 0 else
    integratedPrivatePassing P (E label) (forwardSliceAt p label x)

/-- The literal local false-row bad event, using the proved zeroed true-row
extension over the existing complete forward family. -/
@[expose] noncomputable def falseForwardRareTailBadSet
    {p : Parameters} {s : Fin (n_boot p)} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (E : SliceLabel p → EligibleListFunction p s Ω) (J : Fin (M p)) :
    Set (ForwardFamily p) :=
  {x | (1 / (A_id p : ℝ)) *
      (∑ label : SliceLabel p,
        zeroedIntegratedPrivatePassing P E J label x) >
      1 / ((B_boot p : ℝ) * (n_boot p : ℝ))}

/-- Membership is exactly the nested sum over `v ≠ J` and all ID labels. -/
theorem mem_falseForwardRareTailBadSet_iff
    {p : Parameters} {s : Fin (n_boot p)} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (E : SliceLabel p → EligibleListFunction p s Ω) (J : Fin (M p))
    (x : ForwardFamily p) :
    x ∈ falseForwardRareTailBadSet P E J ↔
      (1 / (A_id p : ℝ)) *
          (∑ v : Fin (M p), ∑ u : Fin (A_id p),
            if v ≠ J then
              integratedPrivatePassing P (E (v, u))
                (forwardSliceAt p (v, u) x)
            else 0) >
        1 / ((B_boot p : ℝ) * (n_boot p : ℝ)) := by
  have hsum :
      (∑ label : SliceLabel p,
        zeroedIntegratedPrivatePassing P E J label x) =
        ∑ v : Fin (M p), ∑ u : Fin (A_id p),
          if v ≠ J then
            integratedPrivatePassing P (E (v, u))
              (forwardSliceAt p (v, u) x)
          else 0 := by
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro v hv
    apply Finset.sum_congr rfl
    intro u hu
    by_cases h : v = J <;> simp [zeroedIntegratedPrivatePassing, h]
  change (1 / (A_id p : ℝ)) *
      (∑ label : SliceLabel p,
        zeroedIntegratedPrivatePassing P E J label x) >
        1 / ((B_boot p : ℝ) * (n_boot p : ℝ)) ↔ _
  rw [hsum]

/-- The fixed-context rare-tail event is measurable in the complete forward
family law. -/
theorem measurableSet_falseForwardRareTailBadSet
    {p : Parameters} {s : Fin (n_boot p)} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (E : SliceLabel p → EligibleListFunction p s Ω) (J : Fin (M p)) :
    MeasurableSet (falseForwardRareTailBadSet P E J) := by
  classical
  let statistic : ForwardFamily p → ℝ := fun x =>
    (1 / (A_id p : ℝ)) *
      ∑ label : SliceLabel p,
        zeroedIntegratedPrivatePassing P E J label x
  have hstat : Measurable statistic := measurable_of_finite _
  have hset :
      falseForwardRareTailBadSet P E J =
        statistic ⁻¹' Set.Ioi
          (1 / ((B_boot p : ℝ) * (n_boot p : ℝ))) := by
    ext x
    rfl
  rw [hset]
  exact hstat measurableSet_Ioi

/-- The zeroed full-family variables are independent by measurable
postcomposition of the accepted integrated-passing family. -/
theorem iIndepFun_zeroedIntegratedPrivatePassing
    {p : Parameters} {s : Fin (n_boot p)} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (E : SliceLabel p → EligibleListFunction p s Ω) (J : Fin (M p)) :
    iIndepFun
      (fun label x => zeroedIntegratedPrivatePassing P E J label x)
      (forwardFamilyMeasure p) := by
  let transform : SliceLabel p → ℝ → ℝ := fun label y =>
    if label.1 = J then 0 else y
  have htransform : ∀ label, Measurable (transform label) := by
    intro label
    by_cases h : label.1 = J
    · simp [transform, h]
    · have htransform_id : transform label = fun y : ℝ => y := by
        funext y
        simp [transform, h]
      rw [htransform_id]
      exact measurable_id
  change iIndepFun
    (fun label x => transform label
      (integratedPrivatePassing P (E label) (forwardSliceAt p label x)))
    (forwardFamilyMeasure p)
  exact (iIndepFun_integratedPrivatePassing_family P E).comp transform htransform

/-- Every zeroed integrated passing weight is measurable. -/
theorem measurable_zeroedIntegratedPrivatePassing
    {p : Parameters} {s : Fin (n_boot p)} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (E : SliceLabel p → EligibleListFunction p s Ω) (J : Fin (M p)) :
    ∀ label, Measurable (fun x : ForwardFamily p =>
      zeroedIntegratedPrivatePassing P E J label x) := by
  intro label
  by_cases h : label.1 = J
  · simp [zeroedIntegratedPrivatePassing, h]
  · have hfun :
        (fun x : ForwardFamily p =>
          zeroedIntegratedPrivatePassing P E J label x) =
          integratedPrivatePassing P (E label) ∘ forwardSliceAt p label := by
      funext x
      simp [zeroedIntegratedPrivatePassing, h, Function.comp_apply]
    rw [hfun]
    exact (measurable_integratedPrivatePassing P (E label)).comp
      (measurable_forwardSliceAt p label)

/-- Every zeroed passing weight lies in the unit interval pointwise. -/
theorem zeroedIntegratedPrivatePassing_mem_unitInterval
    {p : Parameters} {s : Fin (n_boot p)} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (E : SliceLabel p → EligibleListFunction p s Ω) (J : Fin (M p)) :
    ∀ label x, zeroedIntegratedPrivatePassing P E J label x ∈ Set.Icc (0 : ℝ) 1 := by
  intro label x
  by_cases h : label.1 = J
  · simp [zeroedIntegratedPrivatePassing, h]
  · simp only [zeroedIntegratedPrivatePassing, h, Set.mem_Icc]
    exact ⟨integratedPrivatePassing_nonneg P (E label)
      (forwardSliceAt p label x), integratedPrivatePassing_le_one P (E label)
      (forwardSliceAt p label x)⟩

/-- The mean of every zeroed full-family variable is at most the accepted
`exp(-8 b_N)` slice mean, including the zeroed true row. -/
theorem integral_zeroedIntegratedPrivatePassing_le_exp
    {p : Parameters} {s : Fin (n_boot p)} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (E : SliceLabel p → EligibleListFunction p s Ω) (J : Fin (M p)) :
    ∀ label,
      (∫ x : ForwardFamily p,
        zeroedIntegratedPrivatePassing P E J label x ∂forwardFamilyMeasure p) ≤
        Real.exp (-8 * (b_N p : ℝ)) := by
  intro label
  by_cases h : label.1 = J
  · simp [zeroedIntegratedPrivatePassing, h]
    positivity
  · simpa [zeroedIntegratedPrivatePassing, h] using
      integratedPrivatePassing_family_mean_le_exp_bound P (E label) label

/-- The full-family mean sum is bounded by the source rare-tail input. -/
private theorem zeroedIntegratedPrivatePassing_sum_integral_le
    {p : Parameters} {s : Fin (n_boot p)} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (E : SliceLabel p → EligibleListFunction p s Ω) (J : Fin (M p)) :
    (∑ label : SliceLabel p,
      ∫ x : ForwardFamily p,
        zeroedIntegratedPrivatePassing P E J label x ∂forwardFamilyMeasure p) ≤
      (A_id p : ℝ) * localRareTailNu p := by
  have hterm (label : SliceLabel p) :
      (∫ x : ForwardFamily p,
        zeroedIntegratedPrivatePassing P E J label x ∂forwardFamilyMeasure p) ≤
        Real.exp (-8 * (b_N p : ℝ)) :=
    integral_zeroedIntegratedPrivatePassing_le_exp P E J label
  have hNone : 1 ≤ N p := Nat.succ_le_of_lt (N_pos p)
  have hN2N3 : (N p) ^ 2 ≤ (N p) ^ 3 := by
    exact Nat.pow_le_pow_right (Nat.zero_lt_of_lt hNone) (by omega)
  have hM : M p ≤ (N p) ^ 3 :=
    (FalseForwardContextUnion.M_le_N_sq p).trans hN2N3
  have hMreal : (M p : ℝ) ≤ (N p : ℝ) ^ 3 := by exact_mod_cast hM
  have hA_nonneg : (0 : ℝ) ≤ (A_id p : ℝ) := Nat.cast_nonneg _
  have hExp_nonneg : 0 ≤ Real.exp (-8 * (b_N p : ℝ)) := (Real.exp_pos _).le
  calc
    (∑ label : SliceLabel p,
      ∫ x : ForwardFamily p,
        zeroedIntegratedPrivatePassing P E J label x ∂forwardFamilyMeasure p) ≤
      ∑ _label : SliceLabel p, Real.exp (-8 * (b_N p : ℝ)) :=
        Finset.sum_le_sum fun label _ => hterm label
    _ = (M p : ℝ) * (A_id p : ℝ) * Real.exp (-8 * (b_N p : ℝ)) := by
      simp [SliceLabel, mul_assoc]
    _ ≤ (N p : ℝ) ^ 3 * (A_id p : ℝ) *
        Real.exp (-8 * (b_N p : ℝ)) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hMreal hA_nonneg) hExp_nonneg
    _ = (A_id p : ℝ) * localRareTailNu p := by
      simp [localRareTailNu, mul_assoc, mul_comm]

/-- The source ceiling dimensions give `B_boot * n_boot ≤ 2T`. -/
theorem B_boot_mul_n_boot_le_two_T (p : Parameters) :
    B_boot p * n_boot p ≤ 2 * p.T := by
  have hBpos : 0 < (B_boot p : ℝ) := Nat.cast_pos.mpr (B_boot_pos p)
  have hupper := n_boot_real_upper_bound p
  have hprod :
      (B_boot p : ℝ) * (n_boot p : ℝ) < (p.T : ℝ) + (B_boot p : ℝ) := by
    calc
      (B_boot p : ℝ) * (n_boot p : ℝ) <
          (B_boot p : ℝ) * ((p.T : ℝ) / (B_boot p : ℝ) + 1) :=
        mul_lt_mul_of_pos_left hupper hBpos
      _ = (p.T : ℝ) + (B_boot p : ℝ) := by
        rw [mul_add, mul_div_cancel₀ _ hBpos.ne']
        ring
  have hB_le_T : (B_boot p : ℝ) ≤ (p.T : ℝ) := by exact_mod_cast B_boot_le_T p
  have hprod' : (B_boot p : ℝ) * (n_boot p : ℝ) < 2 * (p.T : ℝ) := by
    nlinarith
  exact_mod_cast hprod'.le

/-- Twice the horizon is at most the source constructor size. -/
theorem two_mul_T_le_N (p : Parameters) : 2 * p.T ≤ N p := by
  have hKm : 1 ≤ p.K * p.m :=
    Nat.mul_le_mul (Nat.succ_le_of_lt (K_pos p))
      (Nat.succ_le_of_lt (m_pos p))
  have hfactor : 2 ≤ 2 * p.K * p.m := by
    rw [Nat.mul_assoc]
    exact Nat.mul_le_mul_left 2 hKm
  change 2 * p.T ≤ (2 * p.K * p.m) * (p.T + 1)
  calc
    2 * p.T ≤ 2 * (p.T + 1) := Nat.mul_le_mul_left 2 (Nat.le_succ p.T)
    _ ≤ (2 * p.K * p.m) * (p.T + 1) :=
      Nat.mul_le_mul_right (p.T + 1) hfactor

/-- The fixed-context threshold is at least `1/N`. -/
theorem localEpsilon_ge_inv_N (p : Parameters) :
    1 / (N p : ℝ) ≤ localEpsilon p := by
  have hdenpos : 0 < (B_boot p : ℝ) * (n_boot p : ℝ) :=
    mul_pos (Nat.cast_pos.mpr (B_boot_pos p)) (Nat.cast_pos.mpr (n_boot_pos p))
  have hNpos : 0 < (N p : ℝ) := Nat.cast_pos.mpr (N_pos p)
  have hdenle :
      (B_boot p : ℝ) * (n_boot p : ℝ) ≤ (N p : ℝ) := by
    have hbn : B_boot p * n_boot p ≤ 2 * p.T := B_boot_mul_n_boot_le_two_T p
    have htn : 2 * p.T ≤ N p := two_mul_T_le_N p
    exact_mod_cast hbn.trans htn
  rw [localEpsilon, div_le_div_iff₀ hNpos hdenpos]
  simpa only [one_mul] using hdenle

/-- The alphabet times the fixed-context threshold has the lower bound used
in the Chernoff exponent. -/
theorem A_id_mul_localEpsilon_ge_boot_plus_bits
    (p : Parameters) :
    (A_id p : ℝ) * localEpsilon p ≥
      ((B_boot p : ℝ) + (b_N p : ℝ)) / (2 * (b_N p : ℝ)) := by
  have hBpos : 0 < (B_boot p : ℝ) := Nat.cast_pos.mpr (B_boot_pos p)
  have hnpos : 0 < (n_boot p : ℝ) := Nat.cast_pos.mpr (n_boot_pos p)
  have hbpos : 0 < (b_N p : ℝ) := Nat.cast_pos.mpr (b_N_pos p)
  have hdenpos : 0 < (B_boot p : ℝ) * (n_boot p : ℝ) := mul_pos hBpos hnpos
  have hTprod :
      (p.T : ℝ) * ((B_boot p : ℝ) + (b_N p : ℝ)) ≤
        (A_id p : ℝ) * (b_N p : ℝ) := by
    exact_mod_cast T_mul_boot_plus_b_N_le_A_id_mul_b_N p
  have hBn : (B_boot p : ℝ) * (n_boot p : ℝ) ≤ 2 * (p.T : ℝ) := by
    exact_mod_cast B_boot_mul_n_boot_le_two_T p
  have hcross :
      ((B_boot p : ℝ) + (b_N p : ℝ)) *
          ((B_boot p : ℝ) * (n_boot p : ℝ)) ≤
        (A_id p : ℝ) * (2 * (b_N p : ℝ)) := by
    calc
      ((B_boot p : ℝ) + (b_N p : ℝ)) *
          ((B_boot p : ℝ) * (n_boot p : ℝ)) ≤
        ((B_boot p : ℝ) + (b_N p : ℝ)) * (2 * (p.T : ℝ)) :=
          mul_le_mul_of_nonneg_left hBn (by positivity)
      _ ≤ ((A_id p : ℝ) * (b_N p : ℝ)) * 2 := by
        nlinarith [hTprod]
      _ = (A_id p : ℝ) * (2 * (b_N p : ℝ)) := by ring
  rw [localEpsilon]
  calc
    ((B_boot p : ℝ) + (b_N p : ℝ)) /
        (2 * (b_N p : ℝ)) ≤
      (A_id p : ℝ) / ((B_boot p : ℝ) * (n_boot p : ℝ)) := by
        apply (div_le_div_iff₀
          (mul_pos (by norm_num : (0 : ℝ) < 2) hbpos) hdenpos).2
        nlinarith [hcross]
    _ = (A_id p : ℝ) *
        (1 / ((B_boot p : ℝ) * (n_boot p : ℝ))) := by ring

private theorem b_N_ge_five_of_twentyFour_le_N
    (p : Parameters) (hN : 24 ≤ N p) : 5 ≤ b_N p := by
  by_contra h
  have hb : b_N p ≤ 4 := by omega
  have hD : D p ≤ 16 := by
    unfold D
    exact Nat.pow_le_pow_right (by decide : 1 ≤ 2) hb
  have hND : N p < D p := N_lt_D p
  omega

/-- The natural logarithm of `N` is bounded by `0.7 b_N`, using the actual
ceiling-log dimension and Mathlib's verified bound on `log 2`. -/
private theorem log_N_le_seven_tenths_b_N
    (p : Parameters) : Real.log (N p : ℝ) ≤ (7 / 10 : ℝ) * (b_N p : ℝ) := by
  have hNpos : 0 < (N p : ℝ) := Nat.cast_pos.mpr (N_pos p)
  have hDpos : 0 < (D p : ℝ) := Nat.cast_pos.mpr (D_pos p)
  have hND : (N p : ℝ) < (D p : ℝ) := by exact_mod_cast N_lt_D p
  have hlogD : Real.log (D p : ℝ) = (b_N p : ℝ) * Real.log 2 := by
    rw [D, Nat.cast_pow, Real.log_pow, Nat.cast_ofNat]
  have hlog2 : Real.log 2 ≤ (7 / 10 : ℝ) := by
    exact le_of_lt (lt_trans Real.log_two_lt_d9 (by norm_num))
  apply le_of_lt
  calc
    Real.log (N p : ℝ) < Real.log (D p : ℝ) := Real.log_lt_log hNpos hND
    _ = (b_N p : ℝ) * Real.log 2 := hlogD
    _ ≤ (7 / 10 : ℝ) * (b_N p : ℝ) := by
      calc
        (b_N p : ℝ) * Real.log 2 ≤
            (b_N p : ℝ) * (7 / 10 : ℝ) :=
          mul_le_mul_of_nonneg_left hlog2 (Nat.cast_nonneg _)
        _ = (7 / 10 : ℝ) * (b_N p : ℝ) := by ring

/-- For every `N ≥ 24`, the source logarithmic ratio is at least `5 b_N`. -/
theorem localLogRatio_ge_five_b_N
    (p : Parameters) (hN : 24 ≤ N p) :
    5 * (b_N p : ℝ) ≤
      Real.log (localEpsilon p / (Real.exp 1 * localRareTailNu p)) := by
  have hbNat : 5 ≤ b_N p := b_N_ge_five_of_twentyFour_le_N p hN
  have hb : (5 : ℝ) ≤ (b_N p : ℝ) := by exact_mod_cast hbNat
  have hNpos : 0 < (N p : ℝ) := Nat.cast_pos.mpr (N_pos p)
  have hepspos : 0 < localEpsilon p := by
    unfold localEpsilon
    exact div_pos zero_lt_one (mul_pos
      (Nat.cast_pos.mpr (B_boot_pos p)) (Nat.cast_pos.mpr (n_boot_pos p)))
  have hnu_pos : 0 < localRareTailNu p := by
    rw [localRareTailNu]
    exact mul_pos (pow_pos hNpos 3) (Real.exp_pos _)
  have heps_lower : 1 / (N p : ℝ) ≤ localEpsilon p := localEpsilon_ge_inv_N p
  have hlogN := log_N_le_seven_tenths_b_N p
  have hlogeps : -Real.log (N p : ℝ) ≤ Real.log (localEpsilon p) := by
    have h := Real.log_le_log (by positivity : (0 : ℝ) < 1 / (N p : ℝ)) heps_lower
    rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) (ne_of_gt hNpos), Real.log_one] at h
    simpa using h
  have hlognu : Real.log (localRareTailNu p) =
      3 * Real.log (N p : ℝ) - 8 * (b_N p : ℝ) := by
    rw [localRareTailNu, Real.log_mul (pow_ne_zero 3 (ne_of_gt hNpos))
      (Real.exp_ne_zero _), Real.log_pow, Real.log_exp]
    ring
  have hlog_identity :
      Real.log (localEpsilon p / (Real.exp 1 * localRareTailNu p)) =
        Real.log (localEpsilon p) - 1 -
          (3 * Real.log (N p : ℝ) - 8 * (b_N p : ℝ)) := by
    rw [Real.log_div (ne_of_gt hepspos)
      (mul_ne_zero (Real.exp_ne_zero 1) (ne_of_gt hnu_pos)),
      Real.log_mul (Real.exp_ne_zero 1) (ne_of_gt hnu_pos),
      Real.log_exp, hlognu]
    ring
  rw [hlog_identity]
  nlinarith [hlogeps, hlogN]

/-- A uniform universal threshold and the full fixed-context conclusion.

The quantifier for `N₀` precedes every problem, block, true index, private
probability space, and eligibility family. -/
theorem exists_universal_N0_fixedContext_falseForwardRareTail :
    ∃ N₀ : ℕ, ∀ p : Parameters, N₀ ≤ N p →
      ∀ s : Fin (n_boot p), ∀ J : Fin (M p),
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P],
      ∀ E : SliceLabel p → EligibleListFunction p s Ω,
        MeasurableSet (falseForwardRareTailBadSet P E J) ∧
        (∀ x : ForwardFamily p,
          x ∈ falseForwardRareTailBadSet P E J ↔
            (1 / (A_id p : ℝ)) *
                (∑ v : Fin (M p), ∑ u : Fin (A_id p),
                  if v ≠ J then
                    integratedPrivatePassing P (E (v, u))
                      (forwardSliceAt p (v, u) x)
                  else 0) >
              1 / ((B_boot p : ℝ) * (n_boot p : ℝ))) ∧
        (forwardFamilyMeasure p).real (falseForwardRareTailBadSet P E J) ≤
          Real.exp (-(5 / 2 : ℝ) *
            ((B_boot p : ℝ) + (b_N p : ℝ))) := by
  refine ⟨24, ?_⟩
  intro p hN s J Ω hΩ P hP E
  have hApos : 0 < (A_id p : ℝ) := Nat.cast_pos.mpr (A_id_pos p)
  have hnu_pos : 0 < localRareTailNu p := by
    rw [localRareTailNu]
    exact mul_pos (pow_pos (Nat.cast_pos.mpr (N_pos p)) 3) (Real.exp_pos _)
  have hepspos : 0 < localEpsilon p := by
    unfold localEpsilon
    exact div_pos zero_lt_one (mul_pos
      (Nat.cast_pos.mpr (B_boot_pos p)) (Nat.cast_pos.mpr (n_boot_pos p)))
  have hlog := localLogRatio_ge_five_b_N p hN
  have hlogpos :
      0 < Real.log (localEpsilon p / (Real.exp 1 * localRareTailNu p)) := by
    have hb : 0 < (b_N p : ℝ) := Nat.cast_pos.mpr (b_N_pos p)
    exact lt_of_lt_of_le (by positivity) hlog
  have hratio :
      1 < localEpsilon p / (Real.exp 1 * localRareTailNu p) := by
    have hexp_lt := Real.exp_lt_exp.mpr hlogpos
    simpa [Real.exp_log (div_pos hepspos
      (mul_pos (Real.exp_pos 1) hnu_pos))] using hexp_lt
  have hmul_lt : Real.exp 1 * localRareTailNu p < localEpsilon p :=
    (one_lt_div (mul_pos (Real.exp_pos 1) hnu_pos)).1 hratio
  have hexp1 : 1 < Real.exp 1 := by
    have h := Real.add_one_le_exp (1 : ℝ)
    linarith
  have hnu_eps : localRareTailNu p < localEpsilon p := by
    calc
      localRareTailNu p < Real.exp 1 * localRareTailNu p := by
        simpa only [one_mul] using mul_lt_mul_of_pos_right hexp1 hnu_pos
      _ < localEpsilon p := hmul_lt
  have hXindep := iIndepFun_zeroedIntegratedPrivatePassing P E J
  have hXmeas := measurable_zeroedIntegratedPrivatePassing P E J
  have hXbounds : ∀ label, ∀ᵐ x ∂forwardFamilyMeasure p,
      zeroedIntegratedPrivatePassing P E J label x ∈ Set.Icc (0 : ℝ) 1 := by
    intro label
    exact Filter.Eventually.of_forall
      (zeroedIntegratedPrivatePassing_mem_unitInterval P E J label)
  have hXexpectation := zeroedIntegratedPrivatePassing_sum_integral_le P E J
  have htail := RareTailBound.rareTailBound
    (forwardFamilyMeasure p)
    (fun label x => zeroedIntegratedPrivatePassing P E J label x)
    hXindep hXmeas hXbounds (A_id p : ℝ) (localRareTailNu p)
    (localEpsilon p) hApos hnu_pos hnu_eps hXexpectation
  have hAeps := A_id_mul_localEpsilon_ge_boot_plus_bits p
  have hAeps_nonneg : 0 ≤ (A_id p : ℝ) * localEpsilon p := by positivity
  have hlog_nonneg : 0 ≤ 5 * (b_N p : ℝ) := by positivity
  have hproduct :
      (5 / 2 : ℝ) * ((B_boot p : ℝ) + (b_N p : ℝ)) ≤
        ((A_id p : ℝ) * localEpsilon p) *
          Real.log (localEpsilon p / (Real.exp 1 * localRareTailNu p)) := by
    have heq :
        (5 / 2 : ℝ) * ((B_boot p : ℝ) + (b_N p : ℝ)) =
          (((B_boot p : ℝ) + (b_N p : ℝ)) /
            (2 * (b_N p : ℝ))) * (5 * (b_N p : ℝ)) := by
      field_simp [ne_of_gt (Nat.cast_pos.mpr (b_N_pos p))]
    calc
      (5 / 2 : ℝ) * ((B_boot p : ℝ) + (b_N p : ℝ)) =
          (((B_boot p : ℝ) + (b_N p : ℝ)) /
            (2 * (b_N p : ℝ))) * (5 * (b_N p : ℝ)) := heq
      _ ≤ ((A_id p : ℝ) * localEpsilon p) * (5 * (b_N p : ℝ)) :=
        mul_le_mul_of_nonneg_right hAeps (by positivity)
      _ ≤ ((A_id p : ℝ) * localEpsilon p) *
          Real.log (localEpsilon p / (Real.exp 1 * localRareTailNu p)) :=
        mul_le_mul_of_nonneg_left hlog (by positivity)
  have hset :
      falseForwardRareTailBadSet P E J =
        {x | localEpsilon p <
          (∑ label : SliceLabel p,
            zeroedIntegratedPrivatePassing P E J label x) / (A_id p : ℝ)} := by
    ext x
    change ((1 / (A_id p : ℝ)) *
        (∑ label : SliceLabel p,
          zeroedIntegratedPrivatePassing P E J label x) >
        1 / ((B_boot p : ℝ) * (n_boot p : ℝ))) ↔
      localEpsilon p <
        (∑ label : SliceLabel p,
          zeroedIntegratedPrivatePassing P E J label x) / (A_id p : ℝ)
    have hscale :
        (1 / (A_id p : ℝ)) *
            (∑ label : SliceLabel p,
              zeroedIntegratedPrivatePassing P E J label x) =
          (∑ label : SliceLabel p,
            zeroedIntegratedPrivatePassing P E J label x) / (A_id p : ℝ) := by
      field_simp [ne_of_gt hApos]
    rw [localEpsilon, hscale]
  have hmeasure :
      (forwardFamilyMeasure p).real (falseForwardRareTailBadSet P E J) ≤
        Real.exp (-((A_id p : ℝ) * localEpsilon p) *
          Real.log (localEpsilon p / (Real.exp 1 * localRareTailNu p))) := by
    rw [hset]
    simpa only [Finset.sum_apply] using htail
  refine ⟨measurableSet_falseForwardRareTailBadSet P E J, ?_, ?_⟩
  · exact mem_falseForwardRareTailBadSet_iff P E J
  · calc
      (forwardFamilyMeasure p).real (falseForwardRareTailBadSet P E J) ≤
          Real.exp (-((A_id p : ℝ) * localEpsilon p) *
            Real.log (localEpsilon p / (Real.exp 1 * localRareTailNu p))) := hmeasure
      _ ≤ Real.exp (-(5 / 2 : ℝ) *
          ((B_boot p : ℝ) + (b_N p : ℝ))) :=
        Real.exp_le_exp.mpr (by simpa only [neg_mul] using neg_le_neg hproduct)

end Bandits.Support.ForwardPrefixRareTail

end
