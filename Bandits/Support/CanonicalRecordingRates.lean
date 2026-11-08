/-
Copyright (c) 2026 The Bandits Lean regret formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ConstructorDimensions
public import Bandits.Support.DyadicEnvelope
public import Bandits.Support.ProductMarginalStability
public import Bandits.Support.ProductSetLaw

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Canonical recording rates

The rates in this file are the literal anchor-based rates from
`sources/zip4/manuscript/04_slow_fast_learner.tex:96-138`. Their uniform
envelope consequences use the canonical product-set marginal stability from
`ProductMarginalStability`; the source's stopped-queue moment passage is at
`sources/zip4/manuscript/04_slow_fast_learner.tex:245-290`.

The learning-rate upper bound and positive anchor weights are explicit inputs
to these internal rate lemmas. This module does not define fast-arm laws or
episode weights, and does not assert the source's fast-law feasibility bound.
-/

public section

open scoped BigOperators

namespace Bandits.Support.CanonicalRecordingRates

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ProductSetLaw

/-- The source stability logarithm, represented by the natural ceiling log.
Source: `sources/zip4/manuscript/04_slow_fast_learner.tex:96-99`. -/
@[expose] def L_stab (p : ConstructorDimensions.Parameters) : ℕ :=
  Nat.clog 2 (2 * p.K * (p.T + 1) * (ConstructorDimensions.N p) ^ 2)

/-- The natural ceiling-log form of the source's base-two definition. -/
theorem L_stab_eq_source_ceiling_log (p : ConstructorDimensions.Parameters) :
    L_stab p =
      ⌈Real.logb 2 ((2 * p.K * (p.T + 1) * (ConstructorDimensions.N p) ^ 2 : ℕ) : ℝ)⌉₊ := by
  change Nat.clog 2 (2 * p.K * (p.T + 1) * (ConstructorDimensions.N p) ^ 2) =
    ⌈Real.logb 2 ((2 * p.K * (p.T + 1) * (ConstructorDimensions.N p) ^ 2 : ℕ) : ℝ)⌉₊
  exact (Real.natCeil_logb_natCast 2
    (2 * p.K * (p.T + 1) * (ConstructorDimensions.N p) ^ 2)).symm

private theorem stabArgument_ge_two (p : ConstructorDimensions.Parameters) :
    2 ≤ 2 * p.K * (p.T + 1) * (ConstructorDimensions.N p) ^ 2 := by
  have hK : 1 ≤ p.K := Nat.succ_le_of_lt (ConstructorDimensions.K_pos p)
  have hT : 1 ≤ p.T + 1 := Nat.le_add_left 1 p.T
  have hN : 1 ≤ (ConstructorDimensions.N p) ^ 2 := by
    have hNpos := ConstructorDimensions.N_pos p
    exact Nat.succ_le_of_lt (Nat.pow_pos hNpos)
  calc
    2 = 2 * 1 := by norm_num
    _ ≤ 2 * p.K := Nat.mul_le_mul_left 2 hK
    _ = (2 * p.K) * 1 := by simp
    _ ≤ (2 * p.K) * (p.T + 1) := Nat.mul_le_mul_left (2 * p.K) hT
    _ = (2 * p.K * (p.T + 1)) * 1 := by simp
    _ ≤ (2 * p.K * (p.T + 1)) * (ConstructorDimensions.N p) ^ 2 :=
      Nat.mul_le_mul_left _ hN

/-- The stability logarithm is positive. -/
theorem L_stab_ge_one (p : ConstructorDimensions.Parameters) : 1 ≤ L_stab p := by
  change 1 ≤ Nat.clog 2 (2 * p.K * (p.T + 1) * (ConstructorDimensions.N p) ^ 2)
  exact Nat.succ_le_of_lt (Nat.clog_pos (by decide) (stabArgument_ge_two p))

/-- The natural logarithm used in the queue tail estimate is bounded by
`L_stab`. Source: `sources/zip4/manuscript/04_slow_fast_learner.tex:283-290`. -/
theorem log_stabArgument_le_L_stab (p : ConstructorDimensions.Parameters) :
    Real.log ((2 * p.K * (p.T + 1) *
      (ConstructorDimensions.N p) ^ 2 : ℕ) : ℝ) ≤ (L_stab p : ℝ) := by
  let n : ℕ := 2 * p.K * (p.T + 1) * (ConstructorDimensions.N p) ^ 2
  have hn : 1 < n := Nat.lt_of_succ_le (stabArgument_ge_two p)
  have hx : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hlogx : 0 ≤ Real.log (n : ℝ) :=
    (Real.log_pos hx).le
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2le : Real.log 2 ≤ 1 := by
    calc
      Real.log 2 ≤ 2 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
      _ = 1 := by norm_num
  have hlog_le_logb : Real.log (n : ℝ) ≤ Real.logb 2 (n : ℝ) := by
    rw [Real.logb]
    rw [le_div_iff₀ hlog2pos]
    calc
      Real.log (n : ℝ) * Real.log 2 ≤ Real.log (n : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left hlog2le hlogx
      _ = Real.log (n : ℝ) := by ring
  have hceil : Real.logb 2 (n : ℝ) ≤ (L_stab p : ℝ) := by
    rw [L_stab_eq_source_ceiling_log]
    dsimp [n]
    exact Nat.le_ceil _
  exact hlog_le_logb.trans hceil

/-- The literal stability-scaled learning rate `β = 32 η L_stab`. -/
@[expose] def beta (p : ConstructorDimensions.Parameters) (eta : ℝ) : ℝ :=
  32 * eta * (L_stab p : ℝ)

/-- The literal anchor recording threshold from the source rate formula. -/
@[expose] noncomputable def f (p : ConstructorDimensions.Parameters)
    (v : Fin p.K → ℝ) (i : Fin p.K) : ℝ :=
  ProductSetLaw.theta p.m v i /
    (32 * (p.m : ℝ) *
      ((p.K : ℝ) * ProductSetLaw.theta p.m v i +
        (p.m : ℝ) * (1 - ProductSetLaw.theta p.m v i)))

/-- The literal dyadic recording probability `ξ_i`. -/
@[expose] noncomputable def xi (p : ConstructorDimensions.Parameters) (eta : ℝ)
    (v : Fin p.K → ℝ) (i : Fin p.K) : ℝ :=
  DyadicEnvelope.dyadicCeiling (max (beta p eta) (f p v i))

/-- The literal uniform-exploration probability `γ`. -/
@[expose] def gamma (p : ConstructorDimensions.Parameters) (eta : ℝ) : ℝ :=
  32 * ((p.K - p.m + 1 : ℕ) : ℝ) * beta p eta

/-- The literal source constant controlling the weighted marginal sum. -/
@[expose] def R (p : ConstructorDimensions.Parameters) : ℝ :=
  64 * (p.m : ℝ) ^ 2 * (2 * (p.K : ℝ) - (p.m : ℝ))

private theorem cast_m_pos (p : ConstructorDimensions.Parameters) :
    0 < (p.m : ℝ) := Nat.cast_pos.mpr (ConstructorDimensions.m_pos p)

private theorem cast_K_pos (p : ConstructorDimensions.Parameters) :
    0 < (p.K : ℝ) := Nat.cast_pos.mpr (ConstructorDimensions.K_pos p)

private theorem cast_L_stab_pos (p : ConstructorDimensions.Parameters) :
    0 < (L_stab p : ℝ) := Nat.cast_pos.mpr (Nat.zero_lt_of_lt (L_stab_ge_one p))

private theorem eta_denominator_pos (p : ConstructorDimensions.Parameters) :
    0 < 1024 * (p.m : ℝ) * (p.K : ℝ) * (L_stab p : ℝ) := by
  exact mul_pos
    (mul_pos (mul_pos (by norm_num) (cast_m_pos p)) (cast_K_pos p))
    (cast_L_stab_pos p)

/-- `β` is positive for a positive learning rate. -/
theorem beta_pos (p : ConstructorDimensions.Parameters) {eta : ℝ}
    (heta : 0 < eta) : 0 < beta p eta := by
  unfold beta
  exact mul_pos (mul_pos (by norm_num) heta) (cast_L_stab_pos p)

/-- The source learning-rate restriction, with all dimensions cast to reals,
implies the stated upper bound on `β`. -/
theorem beta_le_one_div_32mK (p : ConstructorDimensions.Parameters)
    {eta : ℝ} (_heta : 0 < eta)
    (heta_le : eta ≤
      1 / (1024 * (p.m : ℝ) * (p.K : ℝ) * (L_stab p : ℝ))) :
    beta p eta ≤ 1 / (32 * (p.m : ℝ) * (p.K : ℝ)) := by
  have hmK : 0 < 32 * (p.m : ℝ) * (p.K : ℝ) :=
    mul_pos (mul_pos (by norm_num) (cast_m_pos p)) (cast_K_pos p)
  have hmKL : 0 < 1024 * (p.m : ℝ) * (p.K : ℝ) * (L_stab p : ℝ) :=
    eta_denominator_pos p
  have hmul := (le_div_iff₀ hmKL).mp heta_le
  unfold beta
  rw [le_div_iff₀ hmK]
  calc
    (32 * eta * (L_stab p : ℝ)) * (32 * (p.m : ℝ) * (p.K : ℝ)) =
        eta * (1024 * (p.m : ℝ) * (p.K : ℝ) * (L_stab p : ℝ)) := by ring
    _ ≤ 1 := hmul

private theorem theta_anchor_pos (p : ConstructorDimensions.Parameters)
    (v : Fin p.K → ℝ) (hvpos : ∀ j, 0 < v j) (i : Fin p.K) :
    0 < ProductSetLaw.theta p.m v i :=
  ProductSetLaw.theta_pos v i (Nat.zero_lt_of_lt (ConstructorDimensions.m_pos p))
    p.m_lt_K hvpos

private theorem theta_anchor_lt_one (p : ConstructorDimensions.Parameters)
    (v : Fin p.K → ℝ) (hvpos : ∀ j, 0 < v j) (i : Fin p.K) :
    ProductSetLaw.theta p.m v i < 1 :=
  ProductSetLaw.theta_lt_one v i (Nat.zero_lt_of_lt (ConstructorDimensions.m_pos p))
    p.m_lt_K hvpos

private theorem f_denominator_pos (p : ConstructorDimensions.Parameters)
    (v : Fin p.K → ℝ) (hvpos : ∀ j, 0 < v j) (i : Fin p.K) :
    0 < 32 * (p.m : ℝ) *
      ((p.K : ℝ) * ProductSetLaw.theta p.m v i +
        (p.m : ℝ) * (1 - ProductSetLaw.theta p.m v i)) := by
  have htheta := theta_anchor_pos p v hvpos i
  have hone_sub := sub_pos.mpr (theta_anchor_lt_one p v hvpos i)
  exact mul_pos (mul_pos (by norm_num) (cast_m_pos p))
    (add_pos (mul_pos (cast_K_pos p) htheta) (mul_pos (cast_m_pos p) hone_sub))

/-- The source threshold `f_i` is positive; its denominator positivity is
derived from the actual canonical inclusion marginal. -/
theorem f_pos (p : ConstructorDimensions.Parameters) (v : Fin p.K → ℝ)
    (hvpos : ∀ j, 0 < v j) (i : Fin p.K) : 0 < f p v i := by
  unfold f
  exact div_pos (theta_anchor_pos p v hvpos i) (f_denominator_pos p v hvpos i)

/-- The source threshold satisfies `f_i ≤ 1/(32 m K)`. -/
theorem f_le_one_div_32mK (p : ConstructorDimensions.Parameters)
    (v : Fin p.K → ℝ) (hvpos : ∀ j, 0 < v j) (i : Fin p.K) :
    f p v i ≤ 1 / (32 * (p.m : ℝ) * (p.K : ℝ)) := by
  have htheta := theta_anchor_pos p v hvpos i
  have htheta_lt := theta_anchor_lt_one p v hvpos i
  have hden := f_denominator_pos p v hvpos i
  have hscale : 0 < 32 * (p.m : ℝ) * (p.K : ℝ) :=
    mul_pos (mul_pos (by norm_num) (cast_m_pos p)) (cast_K_pos p)
  unfold f
  rw [div_le_div_iff₀ hden hscale]
  have hgap : 0 < (p.m : ℝ) * (1 - ProductSetLaw.theta p.m v i) :=
    mul_pos (cast_m_pos p) (sub_pos.mpr htheta_lt)
  nlinarith [hgap]

/-- Dyadic rounding places `β` below `ξ_i`. -/
theorem beta_le_xi (p : ConstructorDimensions.Parameters) {eta : ℝ}
    (heta : 0 < eta) (v : Fin p.K → ℝ) (i : Fin p.K) :
    beta p eta ≤ xi p eta v i := by
  exact (DyadicEnvelope.dyadicCeiling_max_bounds (beta_pos p heta)).1

/-- Every recording probability is strictly positive for positive `η`. -/
theorem xi_pos (p : ConstructorDimensions.Parameters) {eta : ℝ}
    (heta : 0 < eta) (v : Fin p.K → ℝ) (i : Fin p.K) :
    0 < xi p eta v i :=
  (beta_pos p heta).trans_le (beta_le_xi p heta v i)

/-- Dyadic rounding places `f_i` below `ξ_i`. -/
theorem f_le_xi (p : ConstructorDimensions.Parameters) {eta : ℝ}
    (heta : 0 < eta) (v : Fin p.K → ℝ) (i : Fin p.K) :
    f p v i ≤ xi p eta v i := by
  exact ((DyadicEnvelope.dyadicCeiling_max_bounds (beta_pos p heta)).2).1

/-- The strict upper rounding bound for `ξ_i`. -/
theorem xi_lt_two_max (p : ConstructorDimensions.Parameters) {eta : ℝ}
    (heta : 0 < eta) (v : Fin p.K → ℝ) (i : Fin p.K) :
    xi p eta v i < 2 * max (beta p eta) (f p v i) := by
  exact ((DyadicEnvelope.dyadicCeiling_max_bounds (beta_pos p heta)).2).2

/-- The source learning-rate restriction bounds every recording probability. -/
theorem xi_le_one_div_16mK (p : ConstructorDimensions.Parameters)
    {eta : ℝ} (heta : 0 < eta)
    (heta_le : eta ≤
      1 / (1024 * (p.m : ℝ) * (p.K : ℝ) * (L_stab p : ℝ)))
    (v : Fin p.K → ℝ) (hvpos : ∀ j, 0 < v j) (i : Fin p.K) :
    xi p eta v i ≤ 1 / (16 * (p.m : ℝ) * (p.K : ℝ)) := by
  have hbeta := beta_le_one_div_32mK p heta heta_le
  have hf := f_le_one_div_32mK p v hvpos i
  have hmax : max (beta p eta) (f p v i) ≤
      1 / (32 * (p.m : ℝ) * (p.K : ℝ)) := max_le hbeta hf
  have hround := xi_lt_two_max p heta v i
  have hbound : 2 * max (beta p eta) (f p v i) ≤
      1 / (16 * (p.m : ℝ) * (p.K : ℝ)) := by
    calc
      2 * max (beta p eta) (f p v i) ≤
          2 * (1 / (32 * (p.m : ℝ) * (p.K : ℝ))) :=
        mul_le_mul_of_nonneg_left hmax (by norm_num)
      _ = 1 / (16 * (p.m : ℝ) * (p.K : ℝ)) := by ring
  exact le_of_lt (hround.trans_le hbound)

/-- Since `L_stab ≥ 1`, the recorded rate dominates `32 η`. -/
theorem thirtyTwo_mul_eta_le_xi (p : ConstructorDimensions.Parameters)
    {eta : ℝ} (heta : 0 < eta) (v : Fin p.K → ℝ) (i : Fin p.K) :
    32 * eta ≤ xi p eta v i := by
  have hL : (1 : ℝ) ≤ (L_stab p : ℝ) := by
    exact_mod_cast L_stab_ge_one p
  have hbeta : 32 * eta ≤ beta p eta := by
    unfold beta
    calc
      32 * eta = (32 * eta) * 1 := by ring
      _ ≤ (32 * eta) * (L_stab p : ℝ) :=
        mul_le_mul_of_nonneg_left hL (by positivity)
      _ = 32 * eta * (L_stab p : ℝ) := by ring
  exact hbeta.trans (beta_le_xi p heta v i)

/-- All recording rates sum to at most `1/(16m)`. -/
theorem sum_xi_le_one_div_16m (p : ConstructorDimensions.Parameters)
    {eta : ℝ} (heta : 0 < eta)
    (heta_le : eta ≤
      1 / (1024 * (p.m : ℝ) * (p.K : ℝ) * (L_stab p : ℝ)))
    (v : Fin p.K → ℝ) (hvpos : ∀ j, 0 < v j) :
    (∑ i : Fin p.K, xi p eta v i) ≤ 1 / (16 * (p.m : ℝ)) := by
  have hbound := fun i : Fin p.K => xi_le_one_div_16mK p heta heta_le v hvpos i
  have hKpos := cast_K_pos p
  calc
    (∑ i : Fin p.K, xi p eta v i) ≤
        ∑ _i : Fin p.K, 1 / (16 * (p.m : ℝ) * (p.K : ℝ)) :=
      Finset.sum_le_sum fun i hi => hbound i
    _ = (p.K : ℝ) * (1 / (16 * (p.m : ℝ) * (p.K : ℝ))) := by simp
    _ = 1 / (16 * (p.m : ℝ)) := by
      field_simp [ne_of_gt (cast_m_pos p), ne_of_gt hKpos]

/-- In particular, all recording probabilities have total mass at most one. -/
theorem sum_xi_le_one (p : ConstructorDimensions.Parameters)
    {eta : ℝ} (heta : 0 < eta)
    (heta_le : eta ≤
      1 / (1024 * (p.m : ℝ) * (p.K : ℝ) * (L_stab p : ℝ)))
    (v : Fin p.K → ℝ) (hvpos : ∀ j, 0 < v j) :
    (∑ i : Fin p.K, xi p eta v i) ≤ 1 := by
  have hsum := sum_xi_le_one_div_16m p heta heta_le v hvpos
  have hm : (1 : ℝ) ≤ (p.m : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt (ConstructorDimensions.m_pos p)
  have hden : 1 ≤ 16 * (p.m : ℝ) := by nlinarith
  have hfrac : 1 / (16 * (p.m : ℝ)) ≤ 1 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  exact hsum.trans hfrac

/-- The source exploration probability is nonnegative and at most one half. -/
theorem gamma_nonneg_and_le_half (p : ConstructorDimensions.Parameters)
    {eta : ℝ} (heta : 0 < eta)
    (heta_le : eta ≤
      1 / (1024 * (p.m : ℝ) * (p.K : ℝ) * (L_stab p : ℝ))) :
    0 ≤ gamma p eta ∧ gamma p eta ≤ 1 / 2 := by
  have hbeta_pos := beta_pos p heta
  have hbeta_le := beta_le_one_div_32mK p heta heta_le
  have hmKnat : p.K - p.m + 1 ≤ p.K := by
    have hmK := p.m_lt_K
    have hm := p.two_le_m
    omega
  have hfactor_pos : 0 < ((p.K - p.m + 1 : ℕ) : ℝ) := by
    have hmK := p.m_lt_K
    have hm := p.two_le_m
    exact Nat.cast_pos.mpr (Nat.zero_lt_of_lt (by omega : 0 < p.K - p.m + 1))
  have hfactor_le : ((p.K - p.m + 1 : ℕ) : ℝ) ≤ (p.K : ℝ) := by
    exact_mod_cast hmKnat
  have hmpos := cast_m_pos p
  have hKpos := cast_K_pos p
  have hscaled :
      gamma p eta ≤ ((p.K - p.m + 1 : ℕ) : ℝ) /
        ((p.m : ℝ) * (p.K : ℝ)) := by
    unfold gamma
    calc
      32 * ((p.K - p.m + 1 : ℕ) : ℝ) * beta p eta ≤
          32 * ((p.K - p.m + 1 : ℕ) : ℝ) *
            (1 / (32 * (p.m : ℝ) * (p.K : ℝ))) :=
        mul_le_mul_of_nonneg_left hbeta_le (by positivity)
      _ = ((p.K - p.m + 1 : ℕ) : ℝ) /
          ((p.m : ℝ) * (p.K : ℝ)) := by
        field_simp [ne_of_gt hmpos, ne_of_gt hKpos]
  have hfrac :
      ((p.K - p.m + 1 : ℕ) : ℝ) / ((p.m : ℝ) * (p.K : ℝ)) ≤ 1 / 2 := by
    calc
      ((p.K - p.m + 1 : ℕ) : ℝ) / ((p.m : ℝ) * (p.K : ℝ)) ≤
          (p.K : ℝ) / ((p.m : ℝ) * (p.K : ℝ)) :=
        div_le_div_of_nonneg_right hfactor_le (by positivity)
      _ = 1 / (p.m : ℝ) := by
        field_simp [ne_of_gt hmpos, ne_of_gt hKpos]
      _ ≤ 1 / 2 := by
        rw [div_le_iff₀ hmpos]
        have hmcast : (2 : ℝ) ≤ (p.m : ℝ) := by exact_mod_cast p.two_le_m
        nlinarith
  exact ⟨le_of_lt (mul_pos (mul_pos (by norm_num) hfactor_pos) hbeta_pos),
    hscaled.trans hfrac⟩

private theorem anchor_marginal_denominator_le_K
    (p : ConstructorDimensions.Parameters) (v : Fin p.K → ℝ)
    (hvpos : ∀ j, 0 < v j) (i : Fin p.K) :
    (p.K : ℝ) * ProductSetLaw.theta p.m v i +
        (p.m : ℝ) * (1 - ProductSetLaw.theta p.m v i) ≤ (p.K : ℝ) := by
  have htheta_nonneg : 0 ≤ ProductSetLaw.theta p.m v i :=
    (theta_anchor_pos p v hvpos i).le
  have hone_sub_nonneg : 0 ≤ 1 - ProductSetLaw.theta p.m v i :=
    (sub_pos.mpr (theta_anchor_lt_one p v hvpos i)).le
  have hmK : (p.m : ℝ) ≤ (p.K : ℝ) := by
    exact_mod_cast p.m_lt_K.le
  calc
    (p.K : ℝ) * ProductSetLaw.theta p.m v i +
        (p.m : ℝ) * (1 - ProductSetLaw.theta p.m v i) ≤
      (p.K : ℝ) * ProductSetLaw.theta p.m v i +
        (p.K : ℝ) * (1 - ProductSetLaw.theta p.m v i) :=
      add_le_add (le_refl _) (mul_le_mul_of_nonneg_right hmK hone_sub_nonneg)
    _ = (p.K : ℝ) := by ring

private theorem theta_ratio_le_anchor_expression
    (p : ConstructorDimensions.Parameters) {eta : ℝ} (heta : 0 < eta)
    (v w : Fin p.K → ℝ) (hvpos : ∀ j, 0 < v j)
    (henvelope : ∀ j, v j ≤ w j ∧ w j ≤ 2 * v j) (i : Fin p.K) :
    ProductSetLaw.theta p.m w i / xi p eta v i ≤
      64 * (p.m : ℝ) *
        ((p.K : ℝ) * ProductSetLaw.theta p.m v i +
          (p.m : ℝ) * (1 - ProductSetLaw.theta p.m v i)) := by
  have hwpos : ∀ j, 0 < w j := fun j => lt_of_lt_of_le (hvpos j) (henvelope j).1
  have htheta_stability := ProductMarginalStability.theta_le_two_of_coordinatewise_le_two
    v w i (by exact p.two_le_m) p.m_lt_K hvpos hwpos henvelope
  have htheta_v := theta_anchor_pos p v hvpos i
  have htheta_v_lt := theta_anchor_lt_one p v hvpos i
  have hxi_pos := xi_pos p heta v i
  have hf_le := f_le_xi p heta v i
  have hcoef_pos : 0 < 64 * (p.m : ℝ) *
      ((p.K : ℝ) * ProductSetLaw.theta p.m v i +
        (p.m : ℝ) * (1 - ProductSetLaw.theta p.m v i)) := by
    exact mul_pos (mul_pos (by norm_num) (cast_m_pos p))
      (add_pos (mul_pos (cast_K_pos p) htheta_v)
        (mul_pos (cast_m_pos p) (sub_pos.mpr htheta_v_lt)))
  have hcoef_f :
      64 * (p.m : ℝ) *
          ((p.K : ℝ) * ProductSetLaw.theta p.m v i +
            (p.m : ℝ) * (1 - ProductSetLaw.theta p.m v i)) * f p v i =
        2 * ProductSetLaw.theta p.m v i := by
    unfold f
    let d := (p.K : ℝ) * ProductSetLaw.theta p.m v i +
      (p.m : ℝ) * (1 - ProductSetLaw.theta p.m v i)
    have hd : d ≠ 0 := ne_of_gt (by
      dsimp [d]
      exact add_pos (mul_pos (cast_K_pos p) htheta_v)
        (mul_pos (cast_m_pos p) (sub_pos.mpr htheta_v_lt)))
    have hm : (p.m : ℝ) ≠ 0 := ne_of_gt (cast_m_pos p)
    calc
      64 * (p.m : ℝ) * d * (ProductSetLaw.theta p.m v i / (32 * (p.m : ℝ) * d)) =
          (64 * (p.m : ℝ) * d / (32 * (p.m : ℝ) * d)) *
            ProductSetLaw.theta p.m v i := by ring
      _ = 2 * ProductSetLaw.theta p.m v i := by
        rw [show 64 * (p.m : ℝ) * d / (32 * (p.m : ℝ) * d) = 2 by
          field_simp [hm, hd]
          ; ring]
  have htwo_theta_le : 2 * ProductSetLaw.theta p.m v i ≤
      (64 * (p.m : ℝ) *
        ((p.K : ℝ) * ProductSetLaw.theta p.m v i +
          (p.m : ℝ) * (1 - ProductSetLaw.theta p.m v i))) * xi p eta v i := by
    rw [← hcoef_f]
    exact mul_le_mul_of_nonneg_left hf_le hcoef_pos.le
  rw [div_le_iff₀ hxi_pos]
  exact htheta_stability.trans htwo_theta_le

/-- Under the actual canonical product-set law, an anchor-to-current weight
envelope yields the manuscript's per-arm marginal-to-recording-rate bound.
The current weights and coordinatewise envelope remain explicit inputs. -/
theorem theta_div_xi_le_64mK (p : ConstructorDimensions.Parameters)
    {eta : ℝ} (heta : 0 < eta)
    (v w : Fin p.K → ℝ) (hvpos : ∀ j, 0 < v j)
    (henvelope : ∀ j, v j ≤ w j ∧ w j ≤ 2 * v j) (i : Fin p.K) :
    ProductSetLaw.theta p.m w i / xi p eta v i ≤
      64 * (p.m : ℝ) * (p.K : ℝ) := by
  have hexpr := theta_ratio_le_anchor_expression p heta v w hvpos henvelope i
  have hden := anchor_marginal_denominator_le_K p v hvpos i
  calc
    ProductSetLaw.theta p.m w i / xi p eta v i ≤
        64 * (p.m : ℝ) *
          ((p.K : ℝ) * ProductSetLaw.theta p.m v i +
            (p.m : ℝ) * (1 - ProductSetLaw.theta p.m v i)) := hexpr
    _ ≤ 64 * (p.m : ℝ) * (p.K : ℝ) := by
      exact mul_le_mul_of_nonneg_left hden (by positivity)

private theorem sum_one_sub_anchor_theta (p : ConstructorDimensions.Parameters)
    (v : Fin p.K → ℝ) (hvpos : ∀ j, 0 < v j) :
    (∑ i : Fin p.K, (1 - ProductSetLaw.theta p.m v i)) =
      (p.K : ℝ) - (p.m : ℝ) := by
  have hsum := ProductSetLaw.sum_theta_eq_card v
    (Nat.zero_lt_of_lt (ConstructorDimensions.m_pos p)) p.m_lt_K hvpos
  rw [Finset.sum_sub_distrib]
  simp [hsum]

/-- The source weighted marginal sum bound follows by summing the anchor
expression and using `∑ᵢ θ_v(i) = m` for the canonical product-set law. -/
theorem sum_theta_div_xi_le_R (p : ConstructorDimensions.Parameters)
    {eta : ℝ} (heta : 0 < eta)
    (v w : Fin p.K → ℝ) (hvpos : ∀ j, 0 < v j)
    (henvelope : ∀ j, v j ≤ w j ∧ w j ≤ 2 * v j) :
    (∑ i : Fin p.K, ProductSetLaw.theta p.m w i / xi p eta v i) ≤ R p := by
  have hpoint := fun i : Fin p.K =>
    theta_ratio_le_anchor_expression p heta v w hvpos henvelope i
  have hsumtheta := ProductSetLaw.sum_theta_eq_card v
    (Nat.zero_lt_of_lt (ConstructorDimensions.m_pos p)) p.m_lt_K hvpos
  have hsumone := sum_one_sub_anchor_theta p v hvpos
  have hsum_pointwise :
      (∑ i : Fin p.K, 64 * (p.m : ℝ) *
        ((p.K : ℝ) * ProductSetLaw.theta p.m v i +
          (p.m : ℝ) * (1 - ProductSetLaw.theta p.m v i))) = R p := by
    calc
      _ = 64 * (p.m : ℝ) *
          (∑ i : Fin p.K,
            ((p.K : ℝ) * ProductSetLaw.theta p.m v i +
              (p.m : ℝ) * (1 - ProductSetLaw.theta p.m v i))) := by
        rw [Finset.mul_sum]
      _ = 64 * (p.m : ℝ) *
          ((p.K : ℝ) * (p.m : ℝ) +
            (p.m : ℝ) * ((p.K : ℝ) - (p.m : ℝ))) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
          hsumtheta, hsumone]
      _ = R p := by
        unfold R
        ring
  calc
    (∑ i : Fin p.K, ProductSetLaw.theta p.m w i / xi p eta v i) ≤
        ∑ i : Fin p.K, 64 * (p.m : ℝ) *
          ((p.K : ℝ) * ProductSetLaw.theta p.m v i +
            (p.m : ℝ) * (1 - ProductSetLaw.theta p.m v i)) :=
      Finset.sum_le_sum fun i hi => hpoint i
    _ = R p := hsum_pointwise

end Bandits.Support.CanonicalRecordingRates

end
