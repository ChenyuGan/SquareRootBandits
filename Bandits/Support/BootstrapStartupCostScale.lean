/-
Copyright (c) 2026 Bandits contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.BootstrapDimensions
public import Bandits.Support.PublicGridConcentration
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Bootstrap startup cost scale

Literal launch-threshold and bootstrap-cost formulas on the accepted
constructor parameters. Source: `07_public_setup.tex:40-49,144-148` and
`appendix_b_communication.tex:687-720`.
-/

public section

namespace Bandits.Support.BootstrapStartupCostScale

open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.PublicGridConcentration

/-- The source activation threshold `h_boot = ceil(C_h L0 b_N)`.
Source: `sources/zip4/manuscript/07_public_setup.tex:40-49`. -/
@[expose] noncomputable def h_boot (C_h : ℝ) (p : Parameters) : ℕ :=
  ⌈C_h * (L0 p : ℝ) * (b_N p : ℝ)⌉₊

/-- The source launch budget, with both universal constants explicit and
outside the parameter argument. Source: `07_public_setup.tex:40-49`. -/
@[expose] noncomputable def Q (C_star C_h : ℝ) (p : Parameters) : ℕ :=
  ⌈C_star * (
      (p.m : ℝ) ^ 2 * (p.K : ℝ) * (B_boot p : ℝ) * (b_N p : ℝ) +
      (p.m : ℝ) * (h_boot C_h p : ℝ) * (n_boot p : ℝ) +
      (p.m : ℝ) ^ 2 * (h_boot C_h p : ℝ) * (b_N p : ℝ) +
      (p.m : ℝ) * (B_boot p : ℝ))⌉₊

/-- The source bootstrap scale in the product-of-square-roots form
`m * sqrt(m) * sqrt(K T) * b_N^2`.
Source: `sources/zip4/manuscript/07_public_setup.tex:144-148`. -/
@[expose] noncomputable def Q_boot (p : Parameters) : ℝ :=
  (p.m : ℝ) * Real.sqrt (p.m : ℝ) *
    Real.sqrt ((p.K : ℝ) * (p.T : ℝ)) * (b_N p : ℝ) ^ 2

/-- The product form of `Q_boot` is the existing concentration scale `V`
times `b_N`. -/
theorem Q_boot_eq_rowConcentrationScale_mul_b_N (p : Parameters) :
    Q_boot p = rowConcentrationScale p * (b_N p : ℝ) := by
  unfold Q_boot rowConcentrationScale
  ring

/-- The product-of-square-roots form agrees with the source exponent
`m^(3/2)`. -/
theorem Q_boot_eq_source_rpow (p : Parameters) :
    Q_boot p = (p.m : ℝ) ^ (3 / 2 : ℝ) *
      Real.sqrt ((p.K : ℝ) * (p.T : ℝ)) * (b_N p : ℝ) ^ 2 := by
  have hm : 0 < (p.m : ℝ) :=
    Nat.cast_pos.mpr (ConstructorDimensions.m_pos p)
  have hpow : (p.m : ℝ) * Real.sqrt (p.m : ℝ) =
      (p.m : ℝ) ^ (3 / 2 : ℝ) := by
    calc
      (p.m : ℝ) * Real.sqrt (p.m : ℝ) =
          (p.m : ℝ) ^ (1 : ℝ) * (p.m : ℝ) ^ (1 / 2 : ℝ) := by
        rw [Real.rpow_one, ← Real.sqrt_eq_rpow]
      _ = (p.m : ℝ) ^ ((1 : ℝ) + (1 / 2 : ℝ)) :=
        (Real.rpow_add hm _ _).symm
      _ = (p.m : ℝ) ^ (3 / 2 : ℝ) := by congr 1; norm_num
  unfold Q_boot
  rw [hpow]

/-- The real ceiling in `h_boot` is bounded using the accepted dyadic cutoff
estimate `L0 < 4 b_N`. -/
theorem h_boot_real_le (p : Parameters) (C_h : ℝ) (hC_h : 0 ≤ C_h) :
    (h_boot C_h p : ℝ) ≤ (4 * C_h + 1) * (b_N p : ℝ) ^ 2 := by
  let b : ℝ := (b_N p : ℝ)
  have hb1 : 1 ≤ b := by
    dsimp [b]
    exact_mod_cast Nat.succ_le_of_lt (ConstructorDimensions.b_N_pos p)
  have hL0 : (L0 p : ℝ) ≤ 4 * b := by
    dsimp [b]
    exact_mod_cast (BootstrapDimensions.L0_lt_four_mul_b_N p).le
  have hceil : (h_boot C_h p : ℝ) < C_h * (L0 p : ℝ) * b + 1 := by
    unfold h_boot
    exact Nat.ceil_lt_add_one
      (mul_nonneg (mul_nonneg hC_h (Nat.cast_nonneg _)) (Nat.cast_nonneg _))
  calc
    (h_boot C_h p : ℝ) ≤ C_h * (L0 p : ℝ) * b + 1 := hceil.le
    _ ≤ C_h * (4 * b) * b + b ^ 2 := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hL0 hC_h) (Nat.cast_nonneg _)
      · nlinarith [hb1]
    _ = (4 * C_h + 1) * (b_N p : ℝ) ^ 2 := by
      dsimp [b]
      ring

private theorem startupRateIdentity (p : Parameters) :
    (p.m : ℝ) ^ 2 * (p.K : ℝ) *
        Real.sqrt ((p.T : ℝ) / ((p.m : ℝ) * (p.K : ℝ))) =
      (p.m : ℝ) * Real.sqrt (p.m : ℝ) *
        Real.sqrt ((p.K : ℝ) * (p.T : ℝ)) := by
  have hm : 0 < (p.m : ℝ) :=
    Nat.cast_pos.mpr (ConstructorDimensions.m_pos p)
  have hk : 0 < (p.K : ℝ) :=
    Nat.cast_pos.mpr (ConstructorDimensions.K_pos p)
  have ht : 0 < (p.T : ℝ) :=
    Nat.cast_pos.mpr (ConstructorDimensions.T_pos p)
  have hmk : 0 < (p.m : ℝ) * (p.K : ℝ) := mul_pos hm hk
  have hsm : 0 < Real.sqrt (p.m : ℝ) := Real.sqrt_pos.2 hm
  have hsk : 0 < Real.sqrt (p.K : ℝ) := Real.sqrt_pos.2 hk
  have hmkRoot : Real.sqrt ((p.m : ℝ) * (p.K : ℝ)) =
      Real.sqrt (p.m : ℝ) * Real.sqrt (p.K : ℝ) :=
    Real.sqrt_mul hm.le _
  have hktRoot : Real.sqrt ((p.K : ℝ) * (p.T : ℝ)) =
      Real.sqrt (p.K : ℝ) * Real.sqrt (p.T : ℝ) :=
    Real.sqrt_mul hk.le _
  rw [Real.sqrt_div ht.le, hmkRoot, hktRoot]
  field_simp [ne_of_gt hm, ne_of_gt hk, ne_of_gt hsm, ne_of_gt hsk]
  rw [Real.sq_sqrt hm.le, Real.sq_sqrt hk.le]

private theorem startupRootProduct (p : Parameters) :
    Real.sqrt ((p.T : ℝ) / ((p.m : ℝ) * (p.K : ℝ))) *
      Real.sqrt ((p.m : ℝ) * (p.K : ℝ) * (p.T : ℝ)) = (p.T : ℝ) := by
  have hm : 0 ≤ (p.T : ℝ) := Nat.cast_nonneg _
  have hmm : 0 < (p.m : ℝ) :=
    Nat.cast_pos.mpr (ConstructorDimensions.m_pos p)
  have hkk : 0 < (p.K : ℝ) :=
    Nat.cast_pos.mpr (ConstructorDimensions.K_pos p)
  have hmk : 0 < (p.m : ℝ) * (p.K : ℝ) :=
    mul_pos hmm hkk
  have hmul : ((p.T : ℝ) / ((p.m : ℝ) * (p.K : ℝ))) *
      ((p.m : ℝ) * (p.K : ℝ) * (p.T : ℝ)) = (p.T : ℝ) ^ 2 := by
    field_simp [ne_of_gt hmm, ne_of_gt hkk]
  calc
    Real.sqrt ((p.T : ℝ) / ((p.m : ℝ) * (p.K : ℝ))) *
        Real.sqrt ((p.m : ℝ) * (p.K : ℝ) * (p.T : ℝ)) =
      Real.sqrt (((p.T : ℝ) / ((p.m : ℝ) * (p.K : ℝ))) *
        ((p.m : ℝ) * (p.K : ℝ) * (p.T : ℝ))) := by
          symm
          exact Real.sqrt_mul
            (div_nonneg hm (le_of_lt hmk)) ((p.m : ℝ) * (p.K : ℝ) * (p.T : ℝ))
    _ = (p.T : ℝ) := by rw [hmul, Real.sqrt_sq hm]

/-- Under the source large-horizon branch, the full launch budget is bounded
by an explicit coefficient depending only on the three universal constants.
The parameter inputs are exactly `ConstructorDimensions.Parameters`; no scale
bound or other conclusion is assumed. -/
theorem Q_le_cost_scale
    (C_b C_h C_star : ℝ) (p : Parameters)
    (hC_b : 16 ≤ C_b) (hC_h : 0 ≤ C_h) (hC_star : 2 ≤ C_star)
    (hbranch : C_b * (p.m : ℝ) * (p.K : ℝ) *
      (b_N p : ℝ) ^ 2 < (p.T : ℝ)) :
    (Q C_star C_h p : ℝ) ≤
      C_star * (5 + 8 * C_h + (4 * C_h + 1) / Real.sqrt C_b) * Q_boot p := by
  let m : ℝ := (p.m : ℝ)
  let k : ℝ := (p.K : ℝ)
  let t : ℝ := (p.T : ℝ)
  let b : ℝ := (b_N p : ℝ)
  let B : ℝ := (B_boot p : ℝ)
  let n : ℝ := (n_boot p : ℝ)
  let h : ℝ := (h_boot C_h p : ℝ)
  let X : ℝ := Real.sqrt (t / (m * k))
  let Y : ℝ := Real.sqrt (m * k * t)
  let H : ℝ := 4 * C_h + 1
  let q : ℝ := Q_boot p
  let core : ℝ := m ^ 2 * k * B * b + m * h * n + m ^ 2 * h * b + m * B
  have hm : 2 ≤ m := by dsimp [m]; exact_mod_cast p.two_le_m
  have hkNat : 3 ≤ p.K :=
    Nat.succ_le_of_lt (lt_of_le_of_lt p.two_le_m p.m_lt_K)
  have hk : 1 ≤ k := by dsimp [k]; exact_mod_cast (le_trans (by norm_num) hkNat)
  have ht1 : 1 ≤ t := by dsimp [t]; exact_mod_cast p.one_le_T
  have hm0 : 0 ≤ m := by linarith
  have hk0 : 0 ≤ k := by linarith
  have ht0 : 0 ≤ t := by linarith
  have hb1 : 1 ≤ b := by
    dsimp [b]
    exact_mod_cast Nat.succ_le_of_lt (ConstructorDimensions.b_N_pos p)
  have hb0 : 0 ≤ b := by linarith
  have hmPos : 0 < m := by linarith
  have hkPos : 0 < k := by linarith
  have hBPos : 0 < B := by
    dsimp [B]
    exact_mod_cast BootstrapDimensions.B_boot_pos p
  have hB0 : 0 ≤ B := le_of_lt hBPos
  have hn0 : 0 ≤ n := by positivity
  have hh0 : 0 ≤ h := by positivity
  have hBLower : X ≤ B := by
    dsimp [X, B, t, m, k]
    exact BootstrapDimensions.B_boot_real_lower_bound p
  have hBUpper : B < X + 1 := by
    dsimp [X, B, t, m, k]
    exact BootstrapDimensions.B_boot_real_upper_bound p
  have hBootHeight : h ≤ H * b ^ 2 := by
    simpa [h, H, b] using h_boot_real_le p C_h hC_h
  have hCb0 : 0 < C_b := by linarith
  have hdiv : C_b * b ^ 2 < t / (m * k) := by
    apply (lt_div_iff₀ (mul_pos hmPos hkPos)).2
    nlinarith [hbranch]
  have hrootX : Real.sqrt C_b * b ≤ X := by
    calc
      Real.sqrt C_b * b = Real.sqrt (C_b * b ^ 2) := by
        rw [Real.sqrt_mul hCb0.le, Real.sqrt_sq hb0]
      _ ≤ Real.sqrt (t / (m * k)) := Real.sqrt_le_sqrt hdiv.le
      _ = X := rfl
  have hroot4 : 4 ≤ Real.sqrt C_b := by
    have hsixteen : (4 : ℝ) = Real.sqrt 16 := by
      rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [hsixteen]
    exact Real.sqrt_le_sqrt hC_b
  have hX4b : 4 * b ≤ X := by
    calc
      4 * b ≤ Real.sqrt C_b * b := mul_le_mul_of_nonneg_right hroot4 hb0
      _ ≤ X := hrootX
  have hBFiveFour : B ≤ (5 / 4 : ℝ) * X := by
    nlinarith [hBUpper, hX4b, hb1]
  have hrootPos : 0 < Real.sqrt C_b := Real.sqrt_pos.2 hCb0
  have hH0 : 0 ≤ H := by dsimp [H]; positivity
  have hYeq : Y = Real.sqrt m * Real.sqrt (k * t) := by
    dsimp [Y]
    rw [show m * k * t = m * (k * t) by ring, Real.sqrt_mul hm0]
  have hqY : q = m * Y * b ^ 2 := by
    dsimp [q, Q_boot]
    rw [hYeq]
    ring
  have hRate : m ^ 2 * k * X = m * Real.sqrt m * Real.sqrt (k * t) := by
    simpa [m, k, t, X] using startupRateIdentity p
  have hQRate : q = m ^ 2 * k * X * b ^ 2 := by
    dsimp [q, Q_boot]
    calc
      (p.m : ℝ) * Real.sqrt (p.m : ℝ) *
          Real.sqrt ((p.K : ℝ) * (p.T : ℝ)) * b ^ 2 =
        (m ^ 2 * k * X) * b ^ 2 := by rw [← hRate]
      _ = m ^ 2 * k * X * b ^ 2 := by ring
  have hProd : X * Y = t := by
    simpa [X, Y, m, k, t] using startupRootProduct p
  have hY1 : 1 ≤ Y := by
    have hNat : 1 ≤ p.m * p.K * p.T := by
      exact Nat.succ_le_of_lt
        (Nat.mul_pos (Nat.mul_pos (ConstructorDimensions.m_pos p)
          (ConstructorDimensions.K_pos p)) (ConstructorDimensions.T_pos p))
    have hReal : 1 ≤ m * k * t := by
      dsimp [m, k, t]
      exact_mod_cast hNat
    dsimp [Y]
    exact Real.one_le_sqrt.mpr hReal
  have hNRate : t / B ≤ Y := by
    have hTY : t ≤ B * Y := by
      calc
        t = X * Y := hProd.symm
        _ ≤ B * Y := mul_le_mul_of_nonneg_right hBLower (Real.sqrt_nonneg _)
    apply (div_le_iff₀ hBPos).2
    simpa [mul_comm] using hTY
  have hnRaw : n ≤ t / B + 1 := by
    dsimp [n, t, B]
    exact (BootstrapDimensions.n_boot_real_upper_bound p).le
  have hnUpper : n ≤ Y + 1 := by linarith only [hnRaw, hNRate]
  have hnTwoY : n ≤ 2 * Y := by linarith only [hnUpper, hY1]
  have hbSq1 : 1 ≤ b ^ 2 := by nlinarith [hb1]
  have hbLeSq : b ≤ b ^ 2 := by nlinarith [hb1]
  have hA : m ^ 2 * k * B * b ≤ (5 / 4 : ℝ) * q := by
    calc
      m ^ 2 * k * B * b ≤ m ^ 2 * k * ((5 / 4 : ℝ) * X) * b := by
        gcongr
      _ = (5 / 4 : ℝ) * (m ^ 2 * k * X) * b := by ring
      _ ≤ (5 / 4 : ℝ) * (m ^ 2 * k * X) * b ^ 2 :=
        mul_le_mul_of_nonneg_left hbLeSq (by positivity)
      _ = (5 / 4 : ℝ) * q := by rw [hQRate]; ring
  have hm1 : 1 ≤ m := by linarith
  have hmk1 : 1 ≤ m * k := by
    calc
      1 = 1 * 1 := by norm_num
      _ ≤ m * k := mul_le_mul hm1 hk (by norm_num) hm0
  have hcoeff1 : 1 ≤ m * k * b ^ 2 := by
    calc
      1 = 1 * 1 := by norm_num
      _ ≤ (m * k) * b ^ 2 :=
        mul_le_mul hmk1 hbSq1 (by norm_num) (by linarith [hmk1])
  have hMXq : m * X ≤ q := by
    calc
      m * X = 1 * (m * X) := by ring
      _ ≤ (m * k * b ^ 2) * (m * X) :=
        mul_le_mul_of_nonneg_right hcoeff1 (mul_nonneg hm0 (Real.sqrt_nonneg _))
      _ = q := by rw [hQRate]; ring
  have hD : m * B ≤ (5 / 4 : ℝ) * q := by
    calc
      m * B ≤ m * ((5 / 4 : ℝ) * X) := by gcongr
      _ = (5 / 4 : ℝ) * (m * X) := by ring
      _ ≤ (5 / 4 : ℝ) * q :=
        mul_le_mul_of_nonneg_left hMXq (by norm_num)
  have hBcost : m * h * n ≤ 2 * H * q := by
    calc
      m * h * n ≤ m * (H * b ^ 2) * n := by gcongr
      _ ≤ m * (H * b ^ 2) * (2 * Y) := by gcongr
      _ = 2 * H * q := by rw [hqY]; ring
  have hCBase : m ^ 2 * h * b ≤ H * m ^ 2 * b ^ 3 := by
    calc
      m ^ 2 * h * b ≤ m ^ 2 * (H * b ^ 2) * b := by gcongr
      _ = H * m ^ 2 * b ^ 3 := by ring
  have hQRootLower : m ^ 2 * k * Real.sqrt C_b * b ^ 3 ≤ q := by
    calc
      m ^ 2 * k * Real.sqrt C_b * b ^ 3 =
          m ^ 2 * k * (Real.sqrt C_b * b) * b ^ 2 := by ring
      _ ≤ m ^ 2 * k * X * b ^ 2 := by gcongr
      _ = q := hQRate.symm
  have hCScaled : H * m ^ 2 * b ^ 3 ≤ (H / Real.sqrt C_b) * q := by
    calc
      H * m ^ 2 * b ^ 3 ≤ H * m ^ 2 * k * b ^ 3 := by
        have hHmSq : H * m ^ 2 ≤ H * m ^ 2 * k :=
          calc
            H * m ^ 2 = H * m ^ 2 * 1 := by ring
            _ ≤ H * m ^ 2 * k :=
              mul_le_mul_of_nonneg_left hk (mul_nonneg hH0 (sq_nonneg m))
        exact mul_le_mul_of_nonneg_right hHmSq (pow_nonneg hb0 3)
      _ = (H / Real.sqrt C_b) *
          (m ^ 2 * k * Real.sqrt C_b * b ^ 3) := by
        field_simp [ne_of_gt hrootPos]
      _ ≤ (H / Real.sqrt C_b) * q :=
        mul_le_mul_of_nonneg_left hQRootLower
          (div_nonneg hH0 (Real.sqrt_nonneg _))
  have hC : m ^ 2 * h * b ≤ (H / Real.sqrt C_b) * q := hCBase.trans hCScaled
  have hcoreBound : core ≤ (5 / 2 + 2 * H + H / Real.sqrt C_b) * q := by
    dsimp [core]
    calc
      m ^ 2 * k * B * b + m * h * n + m ^ 2 * h * b + m * B ≤
          ((5 / 4 : ℝ) * q + 2 * H * q + (H / Real.sqrt C_b) * q) +
            (5 / 4 : ℝ) * q := by
              exact add_le_add (add_le_add (add_le_add hA hBcost) hC) hD
      _ = (5 / 2 + 2 * H + H / Real.sqrt C_b) * q := by ring
  have hcore0 : 0 ≤ core := by
    dsimp [core]
    positivity
  have hceil : (Q C_star C_h p : ℝ) ≤ C_star * core + 1 := by
    change (⌈C_star * core⌉₊ : ℝ) ≤ C_star * core + 1
    exact (Nat.ceil_lt_add_one (mul_nonneg (by linarith) hcore0)).le
  have hq1 : 1 ≤ q := by
    have hYb : 1 ≤ Y * b ^ 2 := by
      calc
        1 = 1 * 1 := by norm_num
        _ ≤ Y * b ^ 2 := mul_le_mul hY1 hbSq1 (by norm_num) (Real.sqrt_nonneg _)
    calc
      1 = 1 * 1 := by norm_num
      _ ≤ m * (Y * b ^ 2) :=
        mul_le_mul hm1 hYb (by norm_num) hm0
      _ = q := by rw [hqY]; ring
  have hhalfq : 1 ≤ (C_star / 2) * q := by
    calc
      1 = 1 * 1 := by norm_num
      _ ≤ (C_star / 2) * q :=
        mul_le_mul (by linarith) hq1 (by norm_num) (by linarith [hC_star])
  calc
    (Q C_star C_h p : ℝ) ≤ C_star * core + 1 := hceil
    _ ≤ C_star * ((5 / 2 + 2 * H + H / Real.sqrt C_b) * q) + 1 := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hcoreBound (by linarith [hC_star])) le_rfl
    _ ≤ C_star * ((5 / 2 + 2 * H + H / Real.sqrt C_b) * q) +
        (C_star / 2) * q :=
          add_le_add le_rfl hhalfq
    _ = C_star * (5 + 8 * C_h + (4 * C_h + 1) / Real.sqrt C_b) * q := by
      dsimp [H]
      ring

/-- The actual bootstrap arm-observation budget fits below the launch budget
whenever `C_star ≥ 2` and the accepted parameter domain has `m ≥ 2`.
Source: the first summand in `07_public_setup.tex:40-49`. -/
theorem bootstrap_arm_budget_le_Q
    (C_h C_star : ℝ) (p : Parameters) (hC_star : 2 ≤ C_star) :
    p.m * p.K * B_boot p * (4 * b_N p) ≤ Q C_star C_h p := by
  let m : ℝ := (p.m : ℝ)
  let k : ℝ := (p.K : ℝ)
  let B : ℝ := (B_boot p : ℝ)
  let b : ℝ := (b_N p : ℝ)
  let h : ℝ := (h_boot C_h p : ℝ)
  let n : ℝ := (n_boot p : ℝ)
  let core : ℝ := m ^ 2 * k * B * b + m * h * n + m ^ 2 * h * b + m * B
  have hm : 2 ≤ m := by dsimp [m]; exact_mod_cast p.two_le_m
  have hm0 : 0 ≤ m := by linarith
  have hk0 : 0 ≤ k := by dsimp [k]; positivity
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  have hb0 : 0 ≤ b := by dsimp [b]; positivity
  have hFactor : 4 * m ≤ C_star * m ^ 2 := by
    calc
      4 * m ≤ 2 * m ^ 2 := by nlinarith [hm]
      _ ≤ C_star * m ^ 2 := mul_le_mul_of_nonneg_right hC_star (sq_nonneg m)
  have hTargetCore : m * k * B * (4 * b) ≤ C_star * core := by
    have hFirst : m * k * B * (4 * b) ≤ C_star * (m ^ 2 * k * B * b) := by
      calc
        m * k * B * (4 * b) = (4 * m) * (k * B * b) := by ring
        _ ≤ (C_star * m ^ 2) * (k * B * b) :=
          mul_le_mul_of_nonneg_right hFactor
            (mul_nonneg (mul_nonneg hk0 hB0) hb0)
        _ = C_star * (m ^ 2 * k * B * b) := by ring
    have hFirstLeCore : m ^ 2 * k * B * b ≤ core := by
      have hrest : 0 ≤ m * h * n + m ^ 2 * h * b + m * B := by positivity
      calc
        m ^ 2 * k * B * b ≤
            m ^ 2 * k * B * b + (m * h * n + m ^ 2 * h * b + m * B) :=
          le_add_of_nonneg_right hrest
        _ = core := by dsimp [core]; ring
    exact hFirst.trans
      (mul_le_mul_of_nonneg_left hFirstLeCore (by linarith [hC_star]))
  have hCeilLower : C_star * core ≤ (Q C_star C_h p : ℝ) := by
    change C_star * core ≤ (⌈C_star * core⌉₊ : ℝ)
    exact Nat.le_ceil _
  have hReal : m * k * B * (4 * b) ≤ (Q C_star C_h p : ℝ) :=
    hTargetCore.trans hCeilLower
  have hRealCast :
      ((p.m * p.K * B_boot p * (4 * b_N p) : ℕ) : ℝ) ≤
        (Q C_star C_h p : ℝ) := by
    simpa [m, k, B, b] using hReal
  exact_mod_cast hRealCast

end Bandits.Support.BootstrapStartupCostScale

end
