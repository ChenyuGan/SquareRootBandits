/-
Copyright (c) 2026 Bandits Lean regret formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.CanonicalRecordingRates
public import Bandits.Support.ConstructorDimensions
public import Bandits.Support.PublicGridConcentration

import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Concrete source dimensions for regret tuning

This file proves the dimensions and scalar comparisons used by the rational
tuning step in `sources/zip4/manuscript/08_main_theorem.tex:4-24,142-155`.
The stability logarithm is from
`sources/zip4/manuscript/04_slow_fast_learner.tex:96-103`.

These are internal quantitative results. They do not choose the branch rate,
construct its integral denominator, or close a source-facing regret theorem.
-/

public section

namespace Bandits.Support.TuningSourceDimensions

open Bandits.Support.ConstructorDimensions

/-- The literal dyadic tuning dimension from the main theorem.
Source: `sources/zip4/manuscript/08_main_theorem.tex:7`. -/
@[expose] def J (p : Parameters) : ℕ :=
  Nat.clog 2 (Nat.choose p.K p.m + 1) + p.m

/-- The literal regret coefficient, with the universal parameter before the
constructor parameters as in the source choice of `C₁`.
Source: `sources/zip4/manuscript/08_main_theorem.tex:5,7`. -/
@[expose] def W (C1 : ℝ) (p : Parameters) : ℝ :=
  C1 * (p.m : ℝ) ^ 2 * (p.K : ℝ) * (b_N p : ℝ)

/-- `J` is exactly the source ceiling-log dimension. -/
theorem J_eq_source_ceiling_log (p : Parameters) :
    J p =
      ⌈Real.logb (2 : ℕ) ((Nat.choose p.K p.m + 1 : ℕ) : ℝ)⌉₊ + p.m := by
  change Nat.clog 2 (Nat.choose p.K p.m + 1) + p.m = _
  rw [← Real.natCeil_logb_natCast 2 (Nat.choose p.K p.m + 1)]

/-- The binomial coefficient is positive on the constructor domain. -/
private theorem choose_pos (p : Parameters) : 0 < Nat.choose p.K p.m :=
  Nat.choose_pos (Nat.le_of_lt p.m_lt_K)

/-- The dimension includes at least the source additive `m` term. -/
theorem m_le_J (p : Parameters) : p.m ≤ J p := by
  dsimp [J]
  omega

/-- The source dimension is positive. -/
theorem J_pos (p : Parameters) : 0 < J p :=
  (ConstructorDimensions.m_pos p).trans_le (m_le_J p)

private theorem choose_succ_le_two_pow (p : Parameters) :
    Nat.choose p.K p.m + 1 ≤ 2 ^ (p.m * b_N p + 1) := by
  have hchoose : Nat.choose p.K p.m ≤ p.K ^ p.m := Nat.choose_le_pow _ _
  have hK : p.K ≤ N p := ConstructorDimensions.K_le_N p
  have hN : N p ≤ D p := (ConstructorDimensions.N_lt_D p).le
  have hDpow : (D p) ^ p.m = 2 ^ (b_N p * p.m) := by
    rw [D]
    rw [← Nat.pow_mul]
  have hpow : Nat.choose p.K p.m ≤ 2 ^ (p.m * b_N p) := by
    calc
      Nat.choose p.K p.m ≤ p.K ^ p.m := hchoose
      _ ≤ (N p) ^ p.m := Nat.pow_le_pow_left hK _
      _ ≤ (D p) ^ p.m := Nat.pow_le_pow_left hN _
      _ = 2 ^ (p.m * b_N p) := by rw [hDpow, Nat.mul_comm]
  have hpow_pos : 1 ≤ 2 ^ (p.m * b_N p) := Nat.one_le_two_pow
  calc
    Nat.choose p.K p.m + 1 ≤ 2 ^ (p.m * b_N p) + 2 ^ (p.m * b_N p) :=
      Nat.add_le_add hpow hpow_pos
    _ = 2 * 2 ^ (p.m * b_N p) := by ring
    _ = 2 ^ (p.m * b_N p + 1) := by rw [Nat.pow_succ, Nat.mul_comm]

/-- `J` is bounded by three times the source product `m b_N`.
The binomial term uses `Nat.choose_le_pow`, `K ≤ N < D`, and
`Nat.clog_le_of_le_pow`. -/
theorem J_le_three_mul_m_mul_b_N (p : Parameters) :
    J p ≤ 3 * p.m * b_N p := by
  have hclog : Nat.clog 2 (Nat.choose p.K p.m + 1) ≤ p.m * b_N p + 1 :=
    Nat.clog_le_of_le_pow (choose_succ_le_two_pow p)
  have hm : p.m ≤ p.m * b_N p := by
    have hb : 1 ≤ b_N p := Nat.succ_le_of_lt (ConstructorDimensions.b_N_pos p)
    calc
      p.m = p.m * 1 := by simp
      _ ≤ p.m * b_N p := Nat.mul_le_mul_left p.m hb
  have hmb_pos : 1 ≤ p.m * b_N p := by
    exact (Nat.succ_le_of_lt (ConstructorDimensions.m_pos p)).trans hm
  have hsum := Nat.add_le_add hclog hm
  calc
    Nat.clog 2 (Nat.choose p.K p.m + 1) + p.m ≤
        (p.m * b_N p + 1) + (p.m * b_N p) := hsum
    _ ≤ (p.m * b_N p + p.m * b_N p) + (p.m * b_N p) := by
      exact Nat.add_le_add_right
        (Nat.add_le_add_left hmb_pos (p.m * b_N p)) (p.m * b_N p)
    _ = 3 * (p.m * b_N p) := by ring
    _ = 3 * p.m * b_N p := by rw [Nat.mul_assoc]

/-- The source stability argument is bounded by `N^3`, because
`2 K (T+1) ≤ N`; applying `Nat.clog_le_of_le_pow` then gives `L_stab ≤ 3b_N`.
Source: `sources/zip4/manuscript/04_slow_fast_learner.tex:96`. -/
theorem L_stab_le_three_mul_b_N (p : Parameters) :
    CanonicalRecordingRates.L_stab p ≤ 3 * b_N p := by
  let a : ℕ := 2 * p.K * (p.T + 1)
  have hm : 1 ≤ p.m := Nat.succ_le_of_lt (ConstructorDimensions.m_pos p)
  have hfactor : a ≤ N p := by
    calc
      a = a * 1 := by simp
      _ ≤ a * p.m := Nat.mul_le_mul_left a hm
      _ = N p := by
        dsimp [a, ConstructorDimensions.N]
        ring
  have hsource : a * (N p) ^ 2 ≤ (N p) ^ 3 := by
    calc
      a * (N p) ^ 2 ≤ N p * (N p) ^ 2 := Nat.mul_le_mul_right _ hfactor
      _ = (N p) ^ 3 := by ring
  have hNcube : (N p) ^ 3 ≤ (D p) ^ 3 :=
    Nat.pow_le_pow_left (ConstructorDimensions.N_lt_D p).le _
  have hDcube : (D p) ^ 3 = 2 ^ (3 * b_N p) := by
    rw [D]
    rw [← Nat.pow_mul]
    congr 1
    exact Nat.mul_comm (b_N p) 3
  change Nat.clog 2 (2 * p.K * (p.T + 1) * (N p) ^ 2) ≤ 3 * b_N p
  apply Nat.clog_le_of_le_pow
  calc
    2 * p.K * (p.T + 1) * (N p) ^ 2 = a * (N p) ^ 2 := by rfl
    _ ≤ (N p) ^ 3 := hsource
    _ ≤ (D p) ^ 3 := hNcube
    _ = 2 ^ (3 * b_N p) := hDcube

/-- The natural logarithm of the binomial coefficient is bounded by the
source logarithm factor times `J`. -/
theorem log_choose_le_log_two_mul_J (p : Parameters) :
    Real.log (Nat.choose p.K p.m : ℝ) ≤ Real.log 2 * (J p : ℝ) := by
  have hchoose : Nat.choose p.K p.m ≤ 2 ^ Nat.clog 2 (Nat.choose p.K p.m + 1) :=
    (Nat.le_add_right _ _).trans (Nat.le_pow_clog (by norm_num) _)
  have hJexp : Nat.clog 2 (Nat.choose p.K p.m + 1) ≤ J p := by
    dsimp [J]
    exact Nat.le_add_right _ _
  have hpow : Nat.choose p.K p.m ≤ 2 ^ J p :=
    hchoose.trans (Nat.pow_le_pow_right (by norm_num) hJexp)
  have hpow_real : (Nat.choose p.K p.m : ℝ) ≤ ((2 ^ J p : ℕ) : ℝ) := by
    exact_mod_cast hpow
  have hlogpow : Real.log ((2 ^ J p : ℕ) : ℝ) =
      (J p : ℝ) * Real.log 2 := by
    rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
  calc
    Real.log (Nat.choose p.K p.m : ℝ) ≤ Real.log ((2 ^ J p : ℕ) : ℝ) :=
      Real.log_le_log (by exact_mod_cast choose_pos p) hpow_real
    _ = Real.log 2 * (J p : ℝ) := by rw [hlogpow]; ring

private theorem clog_choose_succ_le (p : Parameters) :
    Nat.clog 2 (Nat.choose p.K p.m + 1) ≤ Nat.clog 2 (Nat.choose p.K p.m) + 1 := by
  have hchoose : 1 ≤ Nat.choose p.K p.m := Nat.succ_le_of_lt (choose_pos p)
  have hdouble : Nat.choose p.K p.m + 1 ≤ 2 * Nat.choose p.K p.m := by omega
  have hpow : Nat.choose p.K p.m + 1 ≤
      2 ^ (Nat.clog 2 (Nat.choose p.K p.m) + 1) := by
    calc
      Nat.choose p.K p.m + 1 ≤ 2 * Nat.choose p.K p.m := hdouble
      _ ≤ 2 * 2 ^ Nat.clog 2 (Nat.choose p.K p.m) :=
        Nat.mul_le_mul_left 2 (Nat.le_pow_clog (by norm_num) _)
      _ = 2 ^ (Nat.clog 2 (Nat.choose p.K p.m) + 1) := by
        rw [Nat.pow_succ, Nat.mul_comm]
  exact Nat.clog_le_of_le_pow hpow

/-- A fixed reverse comparator, with the explicit universal constant
`C = 2 / log 2`:
`J ≤ C (log (choose K m) + m)`. -/
theorem J_le_two_div_log_two_mul_log_choose_add_m (p : Parameters) :
    (J p : ℝ) ≤ (2 / Real.log 2) *
      (Real.log (Nat.choose p.K p.m : ℝ) + (p.m : ℝ)) := by
  let n : ℕ := Nat.choose p.K p.m
  have hn : 1 ≤ n := Nat.succ_le_of_lt (choose_pos p)
  have hnreal : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hlog_nonneg : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hnreal
  have hceil_nonneg : 0 ≤ Real.logb 2 (n : ℝ) :=
    Real.logb_nonneg (by norm_num) hnreal
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2_le : Real.log 2 ≤ 1 := by
    calc
      Real.log 2 ≤ 2 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
      _ = 1 := by norm_num
  have hclog_cast :
      (Nat.clog 2 (n + 1) : ℝ) ≤ (Nat.clog 2 n : ℝ) + 1 := by
    exact_mod_cast clog_choose_succ_le p
  have hceil_clog : (Nat.clog 2 n : ℝ) < Real.logb 2 (n : ℝ) + 1 := by
    rw [← Real.natCeil_logb_natCast 2 n]
    exact Nat.ceil_lt_add_one hceil_nonneg
  have hdimension : (J p : ℝ) ≤ (p.m : ℝ) + Real.logb 2 (n : ℝ) + 2 := by
    rw [J, Nat.cast_add]
    linarith only [hclog_cast, hceil_clog]
  have hlogb : Real.logb 2 (n : ℝ) = Real.log (n : ℝ) / Real.log 2 := rfl
  have hcoeff : 2 ≤ 2 / Real.log 2 := by
    rw [le_div_iff₀ hlog2]
    nlinarith only [hlog2_le]
  have hcoeff_one : 1 ≤ 2 / Real.log 2 := by linarith
  have hm2 : (2 : ℝ) ≤ (p.m : ℝ) := by exact_mod_cast p.two_le_m
  have hm_bound : (p.m : ℝ) + 2 ≤ 2 * (p.m : ℝ) := by linarith
  have hm_scale : 2 * (p.m : ℝ) ≤ (2 / Real.log 2) * (p.m : ℝ) :=
    mul_le_mul_of_nonneg_right hcoeff (Nat.cast_nonneg _)
  have hlog_coeff : 1 / Real.log 2 ≤ 2 / Real.log 2 := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (by norm_num) (inv_nonneg.mpr hlog2.le)
  have hlog_scale : Real.log (n : ℝ) / Real.log 2 ≤
      (2 / Real.log 2) * Real.log (n : ℝ) := by
    calc
      Real.log (n : ℝ) / Real.log 2 =
          (1 / Real.log 2) * Real.log (n : ℝ) := by ring
      _ ≤ (2 / Real.log 2) * Real.log (n : ℝ) :=
        mul_le_mul_of_nonneg_right hlog_coeff hlog_nonneg
  calc
    (J p : ℝ) ≤ (p.m : ℝ) + Real.logb 2 (n : ℝ) + 2 := hdimension
    _ = ((p.m : ℝ) + 2) + Real.log (n : ℝ) / Real.log 2 := by rw [hlogb]; ring
    _ ≤ 2 * (p.m : ℝ) + (2 / Real.log 2) * Real.log (n : ℝ) :=
      add_le_add hm_bound hlog_scale
    _ ≤ (2 / Real.log 2) * (p.m : ℝ) +
        (2 / Real.log 2) * Real.log (n : ℝ) := add_le_add hm_scale le_rfl
    _ = (2 / Real.log 2) *
        (Real.log (Nat.choose p.K p.m : ℝ) + (p.m : ℝ)) := by
      dsimp [n]
      ring

/-- A positive universal `C₁` makes the literal source coefficient positive. -/
theorem W_pos (C1 : ℝ) (p : Parameters) (hC1 : 0 < C1) : 0 < W C1 p := by
  unfold W
  exact mul_pos
    (mul_pos (mul_pos hC1 (pow_pos (Nat.cast_pos.mpr (ConstructorDimensions.m_pos p)) 2))
      (Nat.cast_pos.mpr (ConstructorDimensions.K_pos p)))
    (Nat.cast_pos.mpr (ConstructorDimensions.b_N_pos p))

/-- The source construction-branch feasibility budget, with a single explicit
positive universal `C₁` shared across all constructor parameters.
Source: `sources/zip4/manuscript/08_main_theorem.tex:5,9-13`. -/
theorem branch_feasibility_budget (C1 : ℝ) (p : Parameters) (hC1 : 0 < C1) :
    ((1024 : ℝ) * (p.m : ℝ) * (p.K : ℝ) *
        (CanonicalRecordingRates.L_stab p : ℝ)) ^ 2 * (J p : ℝ) / W C1 p ≤
      (27 * 1024 ^ 2 / C1) * (p.m : ℝ) * (p.K : ℝ) * (b_N p : ℝ) ^ 2 := by
  have hLnat := L_stab_le_three_mul_b_N p
  have hL : (CanonicalRecordingRates.L_stab p : ℝ) ≤ 3 * (b_N p : ℝ) := by
    exact_mod_cast hLnat
  have hJnat := J_le_three_mul_m_mul_b_N p
  have hJ : (J p : ℝ) ≤ 3 * (p.m : ℝ) * (b_N p : ℝ) := by
    exact_mod_cast hJnat
  have hm : 0 < (p.m : ℝ) := Nat.cast_pos.mpr (ConstructorDimensions.m_pos p)
  have hK : 0 < (p.K : ℝ) := Nat.cast_pos.mpr (ConstructorDimensions.K_pos p)
  have hb : 0 < (b_N p : ℝ) := Nat.cast_pos.mpr (ConstructorDimensions.b_N_pos p)
  have hfactor : 0 < (1024 : ℝ) * (p.m : ℝ) * (p.K : ℝ) := by positivity
  have hbase :
      (1024 : ℝ) * (p.m : ℝ) * (p.K : ℝ) *
          (CanonicalRecordingRates.L_stab p : ℝ) ≤
        (1024 : ℝ) * (p.m : ℝ) * (p.K : ℝ) * (3 * (b_N p : ℝ)) :=
    mul_le_mul_of_nonneg_left hL hfactor.le
  have hbase_nonneg : 0 ≤
      (1024 : ℝ) * (p.m : ℝ) * (p.K : ℝ) *
        (CanonicalRecordingRates.L_stab p : ℝ) := by positivity
  have hbase_upper_nonneg : 0 ≤
      (1024 : ℝ) * (p.m : ℝ) * (p.K : ℝ) * (3 * (b_N p : ℝ)) := by positivity
  have hbase_sq :
      ((1024 : ℝ) * (p.m : ℝ) * (p.K : ℝ) *
          (CanonicalRecordingRates.L_stab p : ℝ)) ^ 2 ≤
        ((1024 : ℝ) * (p.m : ℝ) * (p.K : ℝ) *
          (3 * (b_N p : ℝ))) ^ 2 := by
    nlinarith only [hbase, hbase_nonneg, hbase_upper_nonneg]
  have hbase_upper_sq_nonneg : 0 ≤
      ((1024 : ℝ) * (p.m : ℝ) * (p.K : ℝ) * (3 * (b_N p : ℝ))) ^ 2 := by
    positivity
  have hnum :
      ((1024 : ℝ) * (p.m : ℝ) * (p.K : ℝ) *
          (CanonicalRecordingRates.L_stab p : ℝ)) ^ 2 * (J p : ℝ) ≤
        27 * 1024 ^ 2 * (p.m : ℝ) ^ 3 * (p.K : ℝ) ^ 2 * (b_N p : ℝ) ^ 3 := by
    calc
      _ ≤ ((1024 : ℝ) * (p.m : ℝ) * (p.K : ℝ) *
          (3 * (b_N p : ℝ))) ^ 2 * (J p : ℝ) :=
        mul_le_mul_of_nonneg_right hbase_sq (Nat.cast_nonneg _)
      _ ≤ ((1024 : ℝ) * (p.m : ℝ) * (p.K : ℝ) *
          (3 * (b_N p : ℝ))) ^ 2 *
            (3 * (p.m : ℝ) * (b_N p : ℝ)) :=
        mul_le_mul_of_nonneg_left hJ hbase_upper_sq_nonneg
      _ = 27 * 1024 ^ 2 * (p.m : ℝ) ^ 3 * (p.K : ℝ) ^ 2 *
          (b_N p : ℝ) ^ 3 := by ring
  have hright :
      ((27 * 1024 ^ 2 / C1) * (p.m : ℝ) * (p.K : ℝ) *
          (b_N p : ℝ) ^ 2) * W C1 p =
        27 * 1024 ^ 2 * (p.m : ℝ) ^ 3 * (p.K : ℝ) ^ 2 *
          (b_N p : ℝ) ^ 3 := by
    unfold W
    field_simp [ne_of_gt hC1]
  exact (div_le_iff₀ (W_pos C1 p hC1)).2 (by rw [hright]; exact hnum)

/-- The tuned geometric scale is bounded by the literal public whole-row
concentration scale. -/
theorem sqrt_J_mul_W_mul_T_le_scale (C1 : ℝ) (p : Parameters)
    (hC1 : 0 < C1) :
    Real.sqrt ((J p : ℝ) * W C1 p * (p.T : ℝ)) ≤
      Real.sqrt (3 * C1) * PublicGridConcentration.rowConcentrationScale p := by
  have hm : 0 < (p.m : ℝ) := Nat.cast_pos.mpr (ConstructorDimensions.m_pos p)
  have hK : 0 < (p.K : ℝ) := Nat.cast_pos.mpr (ConstructorDimensions.K_pos p)
  have hT : 0 < (p.T : ℝ) := Nat.cast_pos.mpr (ConstructorDimensions.T_pos p)
  have hb : 0 < (b_N p : ℝ) := Nat.cast_pos.mpr (ConstructorDimensions.b_N_pos p)
  have hW : 0 < W C1 p := W_pos C1 p hC1
  have hJ : (J p : ℝ) ≤ 3 * (p.m : ℝ) * (b_N p : ℝ) := by
    exact_mod_cast J_le_three_mul_m_mul_b_N p
  have hprod :
      (J p : ℝ) * W C1 p * (p.T : ℝ) ≤
        3 * C1 * PublicGridConcentration.rowConcentrationScale p ^ 2 := by
    calc
      (J p : ℝ) * W C1 p * (p.T : ℝ) =
          (J p : ℝ) * (W C1 p * (p.T : ℝ)) := by ring
      _ ≤ (3 * (p.m : ℝ) * (b_N p : ℝ)) * (W C1 p * (p.T : ℝ)) :=
        mul_le_mul_of_nonneg_right hJ (mul_nonneg hW.le hT.le)
      _ = 3 * C1 * PublicGridConcentration.rowConcentrationScale p ^ 2 := by
        rw [W, PublicGridConcentration.rowConcentrationScale_sq]
        ring
  have hscale : 0 ≤ PublicGridConcentration.rowConcentrationScale p :=
    PublicGridConcentration.rowConcentrationScale_nonneg p
  have hC : 0 < 3 * C1 := by positivity
  have hsqrt : Real.sqrt (3 * C1 *
      PublicGridConcentration.rowConcentrationScale p ^ 2) =
      Real.sqrt (3 * C1) * PublicGridConcentration.rowConcentrationScale p := by
    rw [Real.sqrt_mul hC.le, Real.sqrt_sq_eq_abs, abs_of_nonneg hscale]
  calc
    Real.sqrt ((J p : ℝ) * W C1 p * (p.T : ℝ)) ≤
        Real.sqrt (3 * C1 * PublicGridConcentration.rowConcentrationScale p ^ 2) :=
      Real.sqrt_le_sqrt hprod
    _ = Real.sqrt (3 * C1) * PublicGridConcentration.rowConcentrationScale p := hsqrt

end Bandits.Support.TuningSourceDimensions

end
