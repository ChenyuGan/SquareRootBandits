/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstAdmissionNextDispatch
public import Bandits.Support.RecordedCorrectedWindow

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Bounded integer-score growth for the actual product-set law

For arbitrary initial natural scores, a bounded natural score increment gives
the source logarithmic weight bound and the corresponding domination of each
actual normalized atom on the supported `m`-sets. Source:
`sources/zip4/manuscript/appendix_a_local_protocol.tex:65-77`,
`sources/zip4/manuscript/06_interruptions.tex:389-408`, and
`sources/zip4/manuscript/04_slow_fast_learner.tex:140-174`.
-/

public section

open scoped BigOperators

namespace Bandits.Support.BoundedScoreProductDomination

open Bandits.Support

private theorem sourceHazard_le_quarter
    {p : ConstructorDimensions.Parameters}
    (rate : ReferenceActivePhysicalStep.RateInput p) :
    4 * (p.m : ℝ) * rate.eta.val ≤ 1 / 4 := by
  have hKLnat : 1 ≤ p.K * CanonicalRecordingRates.L_stab p := by
    have hK : 1 ≤ p.K := Nat.one_le_of_lt (ConstructorDimensions.K_pos p)
    have hL : 1 ≤ CanonicalRecordingRates.L_stab p :=
      CanonicalRecordingRates.L_stab_ge_one p
    exact Nat.mul_le_mul hK hL
  have hKL : (1 : ℝ) ≤ (p.K : ℝ) * (CanonicalRecordingRates.L_stab p : ℝ) := by
    exact_mod_cast hKLnat
  have hLpos : (0 : ℝ) < (CanonicalRecordingRates.L_stab p : ℝ) := by
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one
      (CanonicalRecordingRates.L_stab_ge_one p)
  have hden : 0 < 1024 * (p.m : ℝ) * (p.K : ℝ) *
      (CanonicalRecordingRates.L_stab p : ℝ) := by
    exact mul_pos
      (mul_pos (mul_pos (by norm_num) (Nat.cast_pos.mpr (ConstructorDimensions.m_pos p)))
        (Nat.cast_pos.mpr (ConstructorDimensions.K_pos p)))
      hLpos
  have hcap : rate.eta.val *
      (1024 * (p.m : ℝ) * (p.K : ℝ) *
        (CanonicalRecordingRates.L_stab p : ℝ)) ≤ 1 := by
    exact (le_div_iff₀ hden).mp rate.sourceCap
  have hdenLower : 1024 * (p.m : ℝ) ≤
      1024 * (p.m : ℝ) * (p.K : ℝ) *
        (CanonicalRecordingRates.L_stab p : ℝ) := by
    calc
      1024 * (p.m : ℝ) = (1024 * (p.m : ℝ)) * 1 := by ring
      _ ≤ (1024 * (p.m : ℝ)) *
          ((p.K : ℝ) * (CanonicalRecordingRates.L_stab p : ℝ)) :=
        mul_le_mul_of_nonneg_left hKL (by positivity)
      _ = 1024 * (p.m : ℝ) * (p.K : ℝ) *
          (CanonicalRecordingRates.L_stab p : ℝ) := by ring
  have heta_m : rate.eta.val * (1024 * (p.m : ℝ)) ≤ 1 := by
    calc
      rate.eta.val * (1024 * (p.m : ℝ)) ≤
          rate.eta.val *
            (1024 * (p.m : ℝ) * (p.K : ℝ) *
              (CanonicalRecordingRates.L_stab p : ℝ)) :=
        mul_le_mul_of_nonneg_left hdenLower (le_of_lt rate.eta.property)
      _ ≤ 1 := hcap
  have hm_eta : (p.m : ℝ) * rate.eta.val ≤ 1 / 1024 := by
    calc
      (p.m : ℝ) * rate.eta.val =
          (rate.eta.val * (1024 * (p.m : ℝ))) / 1024 := by
        field_simp
      _ ≤ 1 / 1024 := div_le_div_of_nonneg_right heta_m (by norm_num)
  calc
    4 * (p.m : ℝ) * rate.eta.val = 4 * ((p.m : ℝ) * rate.eta.val) := by ring
    _ ≤ 4 * (1 / 1024) := by gcongr
    _ ≤ 1 / 4 := by norm_num

/-- Bounded nonnegative integer-score growth controls the source weight ratios
and dominates every atom of the actual normalized product-set law. The premise
`hg` is the internal arithmetic interface for a separately proved physical
first-call service bound; this theorem itself uses no queue-state or score
truth premise. -/
theorem bounded_score_product_domination
    {p : ConstructorDimensions.Parameters}
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (z g : Fin p.K → ℕ) (ell : ℕ)
    (hg : ∀ arm, g arm ≤ 4 * rate.n * ell) :
    let b := AssignmentScoreReconstruction.sourceWeightBase p
    let h := 4 * (p.m : ℝ) * rate.eta.val
    let w0 := fun arm => ScoreWeights.scoreWeight b (z arm)
    let w1 := fun arm => ScoreWeights.scoreWeight b (z arm + g arm)
    (∀ arm, 1 ≤ w1 arm / w0 arm ∧
      Real.log (w1 arm / w0 arm) ≤ 4 * rate.eta.val * (ell : ℝ)) ∧
    (∀ S : ProductSetLaw.ProductSet p.K p.m,
      (1 - h) ^ ell * ProductSetLaw.Q p.m w0 S ≤
        ProductSetLaw.Q p.m w1 S) := by
  dsimp only
  let b := AssignmentScoreReconstruction.sourceWeightBase p
  let h := 4 * (p.m : ℝ) * rate.eta.val
  let w0 := fun arm => ScoreWeights.scoreWeight b (z arm)
  let w1 := fun arm => ScoreWeights.scoreWeight b (z arm + g arm)
  have hD : 0 < (ConstructorDimensions.D p : ℝ) :=
    Nat.cast_pos.mpr (ConstructorDimensions.D_pos p)
  have hbpos : 0 < b := AssignmentScoreReconstruction.sourceWeightBase_pos p
  have hbone : 1 ≤ b := by
    exact ScoreWeights.sourceBase_one_le hD
  have hlogb : Real.log b ≤ 1 / (ConstructorDimensions.D p : ℝ) := by
    calc
      Real.log b ≤ b - 1 := Real.log_le_sub_one_of_pos hbpos
      _ = 1 / (ConstructorDimensions.D p : ℝ) := by
        simp only [b, AssignmentScoreReconstruction.sourceWeightBase]
        ring
  have hratio_eq (arm : Fin p.K) :
      w1 arm / w0 arm = b ^ g arm := by
    dsimp [w1, w0]
    exact ScoreWeights.sourceWeight_update_ratio hD (z arm) (g arm)
  have hcoord : ∀ arm, 1 ≤ w1 arm / w0 arm ∧
      Real.log (w1 arm / w0 arm) ≤ 4 * rate.eta.val * (ell : ℝ) := by
    intro arm
    constructor
    · rw [hratio_eq]
      exact one_le_pow₀ hbone
    · rw [hratio_eq, Real.log_pow]
      have hgR : (g arm : ℝ) ≤ 4 * (rate.n : ℝ) * (ell : ℝ) := by
        exact_mod_cast hg arm
      calc
        (g arm : ℝ) * Real.log b ≤
            (g arm : ℝ) * (1 / (ConstructorDimensions.D p : ℝ)) :=
          mul_le_mul_of_nonneg_left hlogb (Nat.cast_nonneg _)
        _ ≤ (4 * (rate.n : ℝ) * (ell : ℝ)) *
            (1 / (ConstructorDimensions.D p : ℝ)) :=
          mul_le_mul_of_nonneg_right hgR (by positivity)
        _ = 4 * rate.eta.val * (ell : ℝ) := by
          rw [rate.n_scale]
          field_simp [ne_of_gt hD]
  have hw0pos : ∀ arm, 0 < w0 arm := by
    intro arm
    exact ScoreWeights.scoreWeight_pos hbpos _
  have hw1pos : ∀ arm, 0 < w1 arm := by
    intro arm
    exact ScoreWeights.scoreWeight_pos hbpos _
  have hcoordWeight : ∀ arm,
      w1 arm ≤ Real.exp (4 * rate.eta.val * (ell : ℝ)) * w0 arm := by
    intro arm
    have hratioPos : 0 < w1 arm / w0 arm := div_pos (hw1pos arm) (hw0pos arm)
    have hratioExp : w1 arm / w0 arm ≤
        Real.exp (4 * rate.eta.val * (ell : ℝ)) := by
      calc
        w1 arm / w0 arm = Real.exp (Real.log (w1 arm / w0 arm)) :=
          (Real.exp_log hratioPos).symm
        _ ≤ Real.exp (4 * rate.eta.val * (ell : ℝ)) :=
          Real.exp_le_exp.mpr (hcoord arm).2
    exact (div_le_iff₀ (hw0pos arm)).mp hratioExp
  have hSetWeight (S : ProductSetLaw.ProductSet p.K p.m) :
      ProductSetLaw.setWeight w1 S.1 ≤
        Real.exp (h * (ell : ℝ)) * ProductSetLaw.setWeight w0 S.1 := by
    have hprod := Finset.prod_le_prod₀
      (s := S.1)
      (fun arm harm => (hw1pos arm).le)
      (fun arm harm => hcoordWeight arm)
    have hcard : S.1.card = p.m :=
      (Finset.mem_powersetCard.mp S.2).2
    change (∏ arm ∈ S.1, w1 arm) ≤ _
    calc
      (∏ arm ∈ S.1, w1 arm) ≤
          ∏ arm ∈ S.1,
            (Real.exp (4 * rate.eta.val * (ell : ℝ)) * w0 arm) := hprod
      _ = Real.exp (4 * rate.eta.val * (ell : ℝ)) ^ S.1.card *
          ProductSetLaw.setWeight w0 S.1 := by
        simp [ProductSetLaw.setWeight, Finset.prod_mul_distrib]
      _ = Real.exp (h * (ell : ℝ)) * ProductSetLaw.setWeight w0 S.1 := by
        rw [hcard]
        calc
          Real.exp (4 * rate.eta.val * (ell : ℝ)) ^ p.m *
              ProductSetLaw.setWeight w0 S.1 =
            Real.exp ((p.m : ℝ) * (4 * rate.eta.val * (ell : ℝ))) *
              ProductSetLaw.setWeight w0 S.1 := by
                congr 1
                exact (Real.exp_nat_mul (4 * rate.eta.val * (ell : ℝ)) p.m).symm
          _ = Real.exp (h * (ell : ℝ)) * ProductSetLaw.setWeight w0 S.1 := by
            congr 1
            dsimp [h]
            ring_nf
  have hNormalizer :
      ProductSetLaw.normalizer p.m w1 ≤
        Real.exp (h * (ell : ℝ)) * ProductSetLaw.normalizer p.m w0 := by
    rw [ProductSetLaw.normalizer_eq_support_sum,
      ProductSetLaw.normalizer_eq_support_sum]
    calc
      (∑ S ∈ ProductSetLaw.support p.K p.m,
          ProductSetLaw.setWeight w1 S) ≤
        ∑ S ∈ ProductSetLaw.support p.K p.m,
          Real.exp (h * (ell : ℝ)) * ProductSetLaw.setWeight w0 S := by
        apply Finset.sum_le_sum
        intro S hS
        exact hSetWeight ⟨S, hS⟩
      _ = Real.exp (h * (ell : ℝ)) *
          ∑ S ∈ ProductSetLaw.support p.K p.m,
            ProductSetLaw.setWeight w0 S := by
        rw [Finset.mul_sum]
  have hZ0pos : 0 < ProductSetLaw.normalizer p.m w0 :=
    ProductSetLaw.normalizer_pos w0 (ConstructorDimensions.m_pos p) p.m_lt_K hw0pos
  have hZ1pos : 0 < ProductSetLaw.normalizer p.m w1 :=
    ProductSetLaw.normalizer_pos w1 (ConstructorDimensions.m_pos p) p.m_lt_K hw1pos
  have hSetWeight_mono (S : ProductSetLaw.ProductSet p.K p.m) :
      ProductSetLaw.setWeight w0 S.1 ≤ ProductSetLaw.setWeight w1 S.1 := by
    have hprod := Finset.prod_le_prod₀
      (s := S.1)
      (fun arm harm => (hw0pos arm).le)
      (fun arm harm => by
        have hmul := (le_div_iff₀ (hw0pos arm)).mp (hcoord arm).1
        simpa using hmul)
    exact hprod
  have hQexp (S : ProductSetLaw.ProductSet p.K p.m) :
      Real.exp (-(h * (ell : ℝ))) * ProductSetLaw.Q p.m w0 S ≤
        ProductSetLaw.Q p.m w1 S := by
    have hnumerator := hSetWeight_mono S
    have hdiv :
        ProductSetLaw.setWeight w0 S.1 /
            (Real.exp (h * (ell : ℝ)) * ProductSetLaw.normalizer p.m w0) ≤
          ProductSetLaw.setWeight w1 S.1 /
            ProductSetLaw.normalizer p.m w1 := by
      exact div_le_div₀
        (ProductSetLaw.setWeight_pos w1 hw1pos S.1).le
        hnumerator hZ1pos hNormalizer
    have hident :
        ProductSetLaw.Q p.m w0 S * Real.exp (-(h * (ell : ℝ))) =
          ProductSetLaw.setWeight w0 S.1 /
            (Real.exp (h * (ell : ℝ)) * ProductSetLaw.normalizer p.m w0) := by
      rw [ProductSetLaw.Q]
      change (ProductSetLaw.setWeight w0 S.1 /
          ProductSetLaw.normalizer p.m w0) * Real.exp (-(h * (ell : ℝ))) = _
      rw [Real.exp_neg]
      field_simp [hZ0pos.ne', Real.exp_ne_zero]
    calc
      Real.exp (-(h * (ell : ℝ))) * ProductSetLaw.Q p.m w0 S =
          ProductSetLaw.Q p.m w0 S * Real.exp (-(h * (ell : ℝ))) := mul_comm _ _
      _ = ProductSetLaw.setWeight w0 S.1 /
          (Real.exp (h * (ell : ℝ)) * ProductSetLaw.normalizer p.m w0) := hident
      _ ≤ ProductSetLaw.setWeight w1 S.1 /
          ProductSetLaw.normalizer p.m w1 := hdiv
      _ = ProductSetLaw.Q p.m w1 S := rfl
  constructor
  · exact hcoord
  · intro S
    have hquarter : h ≤ 1 / 4 := by
      dsimp [h]
      exact sourceHazard_le_quarter rate
    have hpow : (1 - h) ^ ell ≤ Real.exp (-(h * (ell : ℝ))) := by
      calc
        (1 - h) ^ ell ≤ Real.exp (-h) ^ ell :=
          pow_le_pow_left₀ (sub_nonneg.mpr (by linarith [hquarter]))
            (Real.one_sub_le_exp_neg h) ell
        _ = Real.exp (-(h * (ell : ℝ))) := by
          calc
            Real.exp (-h) ^ ell = Real.exp ((ell : ℝ) * (-h)) :=
              (Real.exp_nat_mul (-h) ell).symm
            _ = Real.exp (-(h * (ell : ℝ))) := by congr 1; ring
    have hQnonneg : 0 ≤ ProductSetLaw.Q p.m w0 S :=
      (ProductSetLaw.Q_pos w0 (ConstructorDimensions.m_pos p) p.m_lt_K
        hw0pos S).le
    calc
      (1 - h) ^ ell * ProductSetLaw.Q p.m w0 S ≤
          Real.exp (-(h * (ell : ℝ))) * ProductSetLaw.Q p.m w0 S :=
        mul_le_mul_of_nonneg_right hpow hQnonneg
      _ ≤ ProductSetLaw.Q p.m w1 S := hQexp S

end Bandits.Support.BoundedScoreProductDomination
