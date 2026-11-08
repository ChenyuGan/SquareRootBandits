/-
Copyright (c) 2026 Bandits Lean regret formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.SourceDyadicTuning
public import Bandits.Support.TuningSourceDimensions
public import Bandits.Support.BootstrapStartupCostScale
public import Bandits.Support.BootstrapDimensions
public import Bandits.Support.PublicGridConcentration
public import Bandits.Support.SmallRegimeAbsorption

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Tuned numerical remainder

This module bounds only the literal numerical remainder in
`sources/zip4/manuscript/08_main_theorem.tex:142-166`. It uses the construction
branch from `sources/zip4/manuscript/07_public_setup.tex:15-22`, the source
block length from lines 15-18, and the literal startup scale from lines
144-148. It proves no physical startup, transport, learning, event, coupling,
or regret statement.
-/

public section

namespace Bandits.Support.TunedNumericalRemainder

open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions

/-- The explicit numerical expression from the final-term calculation in the
main theorem. The rate is the literal accepted dyadic source rate at the same
`C1` used by `W`. Source: `08_main_theorem.tex:142-155`. -/
@[expose] noncomputable def tunedNumericalRemainder (C1 : ℝ) (hC1 : 0 < C1)
    (p : Parameters) : ℝ :=
  BootstrapStartupCostScale.Q_boot p +
    (p.m : ℝ) * (p.K : ℝ) * (b_N p : ℝ) +
    PublicGridConcentration.rowConcentrationScale p +
    (TuningSourceDimensions.J p : ℝ) /
      SourceDyadicTuning.sourceRate C1 hC1 p +
    TuningSourceDimensions.W C1 p * SourceDyadicTuning.sourceRate C1 hC1 p *
      (p.T : ℝ) +
    (p.m : ℝ) * (p.T : ℝ) /
      (SourceDyadicTuning.sourceRate C1 hC1 p * (D p : ℝ)) +
    (p.m : ℝ) * (p.T : ℝ) *
      (5 / (N p : ℝ) ^ 2 + 2 / (N p : ℝ) ^ 2 +
        1 / (B_boot p : ℝ))

private theorem m_mul_K_le_rowConcentrationScale_of_branch
    (Cb : ℝ) (hCb : 16 ≤ Cb) (p : Parameters)
    (hbranch : Cb * (p.m : ℝ) * (p.K : ℝ) * (b_N p : ℝ) ^ 2 < (p.T : ℝ)) :
    (p.m : ℝ) * (p.K : ℝ) ≤
      PublicGridConcentration.rowConcentrationScale p := by
  let m : ℝ := p.m
  let k : ℝ := p.K
  let t : ℝ := p.T
  let b : ℝ := b_N p
  have hm1 : 1 ≤ m := by
    dsimp [m]
    exact_mod_cast Nat.succ_le_of_lt (ConstructorDimensions.m_pos p)
  have hm0 : 0 ≤ m := le_trans (by norm_num) hm1
  have hmpos : 0 < m := lt_of_lt_of_le (by norm_num) hm1
  have hk0 : 0 ≤ k := by positivity
  have hkpos : 0 < k := by
    dsimp [k]
    exact_mod_cast ConstructorDimensions.K_pos p
  have hb1 : 1 ≤ b := by
    dsimp [b]
    exact_mod_cast Nat.succ_le_of_lt (ConstructorDimensions.b_N_pos p)
  have hb0 : 0 ≤ b := le_trans (by norm_num) hb1
  have hbpos : 0 < b := lt_of_lt_of_le (by norm_num) hb1
  have ht0 : 0 ≤ t := by positivity
  have hbranchReal : Cb * (m * k * b ^ 2) < t := by
    simpa [m, k, t, b, mul_assoc] using hbranch
  have hbranch16 : 16 * (m * k * b ^ 2) < t := by
    exact (mul_le_mul_of_nonneg_right hCb (by positivity)).trans_lt hbranchReal
  have hmSq : 1 ≤ m ^ 2 := by nlinarith [sq_nonneg (m - 1)]
  have hbSq : 1 ≤ b ^ 2 := by nlinarith [sq_nonneg (b - 1)]
  have hbFourth : 1 ≤ b ^ 4 := by
    calc
      1 ≤ b ^ 2 := hbSq
      _ = 1 * b ^ 2 := by ring
      _ ≤ b ^ 2 * b ^ 2 :=
        mul_le_mul_of_nonneg_right hbSq (sq_nonneg b)
      _ = b ^ 4 := by ring
  have hFactor : 1 ≤ 16 * m ^ 2 * b ^ 4 := by
    calc
      1 = 1 * 1 := by norm_num
      _ ≤ m ^ 2 * b ^ 4 := mul_le_mul hmSq hbFourth (by norm_num) (by positivity)
      _ = 1 * (m ^ 2 * b ^ 4) := by ring
      _ ≤ 16 * (m ^ 2 * b ^ 4) :=
        mul_le_mul_of_nonneg_right (by norm_num : (1 : ℝ) ≤ 16) (by positivity)
      _ = 16 * m ^ 2 * b ^ 4 := by ring
  have hkFactor : k ≤ 16 * m ^ 2 * k * b ^ 4 := by
    calc
      k = 1 * k := by ring
      _ ≤ (16 * m ^ 2 * b ^ 4) * k :=
        mul_le_mul_of_nonneg_right hFactor hk0
      _ = 16 * m ^ 2 * k * b ^ 4 := by ring
  have hWeightedRaw :=
    mul_lt_mul_of_pos_right hbranch16 (mul_pos hmpos (pow_pos hbpos 2))
  have hWeighted : 16 * m ^ 2 * k * b ^ 4 < m * t * b ^ 2 := by
    nlinarith only [hWeightedRaw]
  have hk_lt : k < m * t * b ^ 2 := lt_of_le_of_lt hkFactor hWeighted
  have hk_le : k ≤ m * t * b ^ 2 := hk_lt.le
  have hScaleSq :
      PublicGridConcentration.rowConcentrationScale p ^ 2 =
        m ^ 3 * k * t * b ^ 2 := by
    simpa [m, k, t, b] using PublicGridConcentration.rowConcentrationScale_sq p
  have hSquare :
      (m * k) ^ 2 ≤ PublicGridConcentration.rowConcentrationScale p ^ 2 := by
    rw [hScaleSq]
    calc
      (m * k) ^ 2 = k * (m ^ 2 * k) := by ring
      _ ≤ (m * t * b ^ 2) * (m ^ 2 * k) :=
        mul_le_mul_of_nonneg_right hk_le (mul_nonneg (sq_nonneg m) hk0)
      _ = m ^ 3 * k * t * b ^ 2 := by ring
  have hmk0 : 0 ≤ m * k := mul_nonneg hm0 hk0
  have hScale0 : 0 ≤ PublicGridConcentration.rowConcentrationScale p :=
    PublicGridConcentration.rowConcentrationScale_nonneg p
  exact (sq_le_sq₀ hmk0 hScale0).mp hSquare

/-- On the strict source construction branch, the arm-bit term is bounded by
the literal startup scale. The branch coefficient need only satisfy the
uniform lower bound already supplied by `sourceRate_uniform_tuning`.
Source: `08_main_theorem.tex:156` and `07_public_setup.tex:15-18,144-148`. -/
theorem m_mul_K_mul_b_N_le_Q_boot_of_construction_branch
    (Cb : ℝ) (hCb : 16 ≤ Cb) (p : Parameters)
    (hbranch : Cb * (p.m : ℝ) * (p.K : ℝ) * (b_N p : ℝ) ^ 2 < (p.T : ℝ)) :
    (p.m : ℝ) * (p.K : ℝ) * (b_N p : ℝ) ≤
      BootstrapStartupCostScale.Q_boot p := by
  have hmk := m_mul_K_le_rowConcentrationScale_of_branch Cb hCb p hbranch
  have hb0 : 0 ≤ (b_N p : ℝ) := by positivity
  calc
    (p.m : ℝ) * (p.K : ℝ) * (b_N p : ℝ) ≤
        PublicGridConcentration.rowConcentrationScale p * (b_N p : ℝ) := by
      exact mul_le_mul_of_nonneg_right hmk hb0
    _ = BootstrapStartupCostScale.Q_boot p :=
      (BootstrapStartupCostScale.Q_boot_eq_rowConcentrationScale_mul_b_N p).symm

/-- The literal public concentration scale is at most `Q_boot`, since
`Q_boot = V b_N` and the accepted bit length is positive. -/
theorem rowConcentrationScale_le_Q_boot (p : Parameters) :
    PublicGridConcentration.rowConcentrationScale p ≤
      BootstrapStartupCostScale.Q_boot p := by
  have hb1 : 1 ≤ (b_N p : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt (ConstructorDimensions.b_N_pos p)
  have hV0 := PublicGridConcentration.rowConcentrationScale_nonneg p
  calc
    PublicGridConcentration.rowConcentrationScale p =
        PublicGridConcentration.rowConcentrationScale p * 1 := by ring
    _ ≤ PublicGridConcentration.rowConcentrationScale p * (b_N p : ℝ) :=
      mul_le_mul_of_nonneg_left hb1 hV0
    _ = BootstrapStartupCostScale.Q_boot p :=
      (BootstrapStartupCostScale.Q_boot_eq_rowConcentrationScale_mul_b_N p).symm

/-- The source ceiling block length bounds the expected false-detection
scale by `m sqrt(m) sqrt(KT)`. This uses the real ceiling lower bound for the
literal `B_boot = ceil(sqrt(T/(mK)))`. Source: `07_public_setup.tex:15-18` and
`08_main_theorem.tex:142-146`. -/
theorem m_mul_T_div_B_boot_le_root_scale (p : Parameters) :
    (p.m : ℝ) * (p.T : ℝ) / (B_boot p : ℝ) ≤
      (p.m : ℝ) * Real.sqrt (p.m : ℝ) *
        Real.sqrt ((p.K : ℝ) * (p.T : ℝ)) := by
  let m : ℝ := p.m
  let k : ℝ := p.K
  let t : ℝ := p.T
  let B : ℝ := B_boot p
  have hm0 : 0 ≤ m := by positivity
  have hmpos : 0 < m := by
    dsimp [m]
    exact_mod_cast ConstructorDimensions.m_pos p
  have hkpos : 0 < k := by
    dsimp [k]
    exact_mod_cast ConstructorDimensions.K_pos p
  have ht0 : 0 ≤ t := by positivity
  have hmkpos : 0 < m * k := mul_pos hmpos hkpos
  have hBpos : 0 < B := by
    dsimp [B]
    exact_mod_cast BootstrapDimensions.B_boot_pos p
  have hBLower : Real.sqrt (t / (m * k)) ≤ B := by
    dsimp [B, t, m, k]
    exact BootstrapDimensions.B_boot_real_lower_bound p
  have hratio0 : 0 ≤ t / (m * k) := by positivity
  have hrootProduct :
      Real.sqrt (t / (m * k)) * Real.sqrt (m * k * t) = t := by
    calc
      Real.sqrt (t / (m * k)) * Real.sqrt (m * k * t) =
          Real.sqrt (t / (m * k) * (m * k * t)) :=
        (Real.sqrt_mul hratio0 (m * k * t)).symm
      _ = Real.sqrt (t ^ 2) := by
        congr 1
        field_simp [ne_of_gt hmkpos]
      _ = t := Real.sqrt_sq ht0
  have htB : t ≤ B * Real.sqrt (m * k * t) := by
    calc
      t = Real.sqrt (t / (m * k)) * Real.sqrt (m * k * t) := hrootProduct.symm
      _ ≤ B * Real.sqrt (m * k * t) :=
        mul_le_mul_of_nonneg_right hBLower (Real.sqrt_nonneg _)
  have hratio_le : t / B ≤ Real.sqrt (m * k * t) :=
    (div_le_iff₀ hBpos).2 (by simpa [mul_comm] using htB)
  calc
    (p.m : ℝ) * (p.T : ℝ) / (B_boot p : ℝ) = m * (t / B) := by
      dsimp [m, t, B]
      ring
    _ ≤ m * Real.sqrt (m * k * t) := mul_le_mul_of_nonneg_left hratio_le hm0
    _ = m * Real.sqrt m * Real.sqrt (k * t) := by
      rw [show m * k * t = m * (k * t) by ring, Real.sqrt_mul hm0]
      ring
    _ = (p.m : ℝ) * Real.sqrt (p.m : ℝ) *
        Real.sqrt ((p.K : ℝ) * (p.T : ℝ)) := by
      rfl

/-- The sum of the two `N^{-2}` source failure allowances is at most seven.
This follows from `mT ≤ N` on the literal constructor dimensions. -/
theorem m_mul_T_mul_seven_div_N_sq_le_seven (p : Parameters) :
    (p.m : ℝ) * (p.T : ℝ) * (7 / (N p : ℝ) ^ 2) ≤ 7 := by
  have hMTN : (p.m : ℝ) * (p.T : ℝ) ≤ (N p : ℝ) := by
    exact_mod_cast SmallRegimeAbsorption.m_mul_T_le_N p
  have hNpos : 0 < (N p : ℝ) :=
    Nat.cast_pos.mpr (ConstructorDimensions.N_pos p)
  have hN1 : 1 ≤ (N p : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt (ConstructorDimensions.N_pos p)
  have hNleSq : (N p : ℝ) ≤ (N p : ℝ) ^ 2 := by
    calc
      (N p : ℝ) = (N p : ℝ) * 1 := by ring
      _ ≤ (N p : ℝ) * (N p : ℝ) :=
        mul_le_mul_of_nonneg_left hN1 (le_of_lt hNpos)
      _ = (N p : ℝ) ^ 2 := by ring
  have hMTleSq : (p.m : ℝ) * (p.T : ℝ) ≤ (N p : ℝ) ^ 2 := hMTN.trans hNleSq
  have hfrac : (p.m : ℝ) * (p.T : ℝ) / (N p : ℝ) ^ 2 ≤ 1 := by
    apply (div_le_iff₀ (pow_pos hNpos 2)).2
    simpa using hMTleSq
  calc
    (p.m : ℝ) * (p.T : ℝ) * (7 / (N p : ℝ) ^ 2) =
        7 * ((p.m : ℝ) * (p.T : ℝ) / (N p : ℝ) ^ 2) := by ring
    _ ≤ 7 := by nlinarith only [hfrac]

/-- The source denominator rounding allowance is at most one. -/
theorem m_mul_T_div_D_le_one (p : Parameters) :
    (p.m : ℝ) * (p.T : ℝ) / (D p : ℝ) ≤ 1 := by
  have hMTN : (p.m : ℝ) * (p.T : ℝ) ≤ (N p : ℝ) := by
    exact_mod_cast SmallRegimeAbsorption.m_mul_T_le_N p
  have hND : (N p : ℝ) ≤ (D p : ℝ) := by
    exact_mod_cast (ConstructorDimensions.N_lt_D p).le
  have hDpos : 0 < (D p : ℝ) :=
    Nat.cast_pos.mpr (ConstructorDimensions.D_pos p)
  apply (div_le_iff₀ hDpos).2
  simpa using hMTN.trans hND

/-- One uniform numerical remainder bound on the strict construction branch.
For each fixed positive `C1`, the shared `Cb,N0` are exactly the witnesses
from `sourceRate_uniform_tuning`; `C = 12 + 6 sqrt(3 C1)` is chosen before
the constructor parameters. The conclusion concerns only the displayed
numerical expression and its original-reward rounding allowance.
Source: `08_main_theorem.tex:142-166` and `07_public_setup.tex:15-22,144-148`.
-/
theorem exists_uniform_tuned_numerical_remainder_bound (C1 : ℝ) (hC1 : 0 < C1) :
    ∃ Cb : ℝ, ∃ N0 : ℕ, ∃ C : ℝ,
      0 < Cb ∧ max 16 (27 * 1024 ^ 2 / C1) ≤ Cb ∧ 0 < C ∧
      ∀ p : Parameters,
        Cb * (p.m : ℝ) * (p.K : ℝ) * (b_N p : ℝ) ^ 2 < (p.T : ℝ) →
        N0 ≤ N p →
        (p.m : ℝ) * (p.K : ℝ) * (b_N p : ℝ) ≤
            BootstrapStartupCostScale.Q_boot p ∧
          PublicGridConcentration.rowConcentrationScale p ≤
            BootstrapStartupCostScale.Q_boot p ∧
          (p.m : ℝ) * (p.T : ℝ) / (B_boot p : ℝ) ≤
            (p.m : ℝ) * Real.sqrt (p.m : ℝ) *
              Real.sqrt ((p.K : ℝ) * (p.T : ℝ)) ∧
          (p.m : ℝ) * (p.T : ℝ) * (7 / (N p : ℝ) ^ 2) ≤ 7 ∧
          (p.m : ℝ) * (p.T : ℝ) / (D p : ℝ) ≤ 1 ∧
          tunedNumericalRemainder C1 hC1 p +
              (p.m : ℝ) * (p.T : ℝ) / (D p : ℝ) ≤
            C * BootstrapStartupCostScale.Q_boot p := by
  obtain ⟨Cb, N0, hCbPos, hCbMax, hUniform⟩ :=
    SourceDyadicTuning.sourceRate_uniform_tuning C1 hC1
  refine ⟨Cb, N0, 12 + 6 * Real.sqrt (3 * C1), hCbPos, hCbMax, ?_, ?_⟩
  · positivity
  · intro p hbranch hN0
    have hRate := hUniform p hbranch hN0
    have hObjective :
        (TuningSourceDimensions.J p : ℝ) /
            SourceDyadicTuning.sourceRate C1 hC1 p +
          TuningSourceDimensions.W C1 p *
            SourceDyadicTuning.sourceRate C1 hC1 p * (p.T : ℝ) ≤
          3 * Real.sqrt (3 * C1) *
            PublicGridConcentration.rowConcentrationScale p :=
      hRate.2.2.2.2.2.2.1
    have hPenalty :
        (p.m : ℝ) * (p.T : ℝ) /
            (SourceDyadicTuning.sourceRate C1 hC1 p * (D p : ℝ)) ≤
          (TuningSourceDimensions.J p : ℝ) /
            SourceDyadicTuning.sourceRate C1 hC1 p :=
      hRate.2.2.2.2.2.2.2
    have hWpos := TuningSourceDimensions.W_pos C1 p hC1
    have hRatePos := SourceDyadicTuning.sourceRate_pos C1 hC1 p
    have hTpos : 0 < (p.T : ℝ) :=
      Nat.cast_pos.mpr (ConstructorDimensions.T_pos p)
    have hSecondNonneg :
        0 ≤ TuningSourceDimensions.W C1 p *
          SourceDyadicTuning.sourceRate C1 hC1 p * (p.T : ℝ) := by
      exact le_of_lt (mul_pos (mul_pos hWpos hRatePos) hTpos)
    have hPenaltyObjective :
        (p.m : ℝ) * (p.T : ℝ) /
            (SourceDyadicTuning.sourceRate C1 hC1 p * (D p : ℝ)) ≤
          (TuningSourceDimensions.J p : ℝ) /
              SourceDyadicTuning.sourceRate C1 hC1 p +
            TuningSourceDimensions.W C1 p *
              SourceDyadicTuning.sourceRate C1 hC1 p * (p.T : ℝ) :=
      hPenalty.trans (le_add_of_nonneg_right hSecondNonneg)
    have hObjectiveAndPenalty :
        ((TuningSourceDimensions.J p : ℝ) /
              SourceDyadicTuning.sourceRate C1 hC1 p +
            TuningSourceDimensions.W C1 p *
              SourceDyadicTuning.sourceRate C1 hC1 p * (p.T : ℝ)) +
            (p.m : ℝ) * (p.T : ℝ) /
              (SourceDyadicTuning.sourceRate C1 hC1 p * (D p : ℝ)) ≤
          6 * Real.sqrt (3 * C1) *
            PublicGridConcentration.rowConcentrationScale p := by
      have hCombined :
          ((TuningSourceDimensions.J p : ℝ) /
                SourceDyadicTuning.sourceRate C1 hC1 p +
              TuningSourceDimensions.W C1 p *
                SourceDyadicTuning.sourceRate C1 hC1 p * (p.T : ℝ)) +
              (p.m : ℝ) * (p.T : ℝ) /
                (SourceDyadicTuning.sourceRate C1 hC1 p * (D p : ℝ)) ≤
            2 * ((TuningSourceDimensions.J p : ℝ) /
                SourceDyadicTuning.sourceRate C1 hC1 p +
              TuningSourceDimensions.W C1 p *
                SourceDyadicTuning.sourceRate C1 hC1 p * (p.T : ℝ)) := by
        nlinarith only [hPenaltyObjective]
      calc
        _ ≤ 2 * ((TuningSourceDimensions.J p : ℝ) /
              SourceDyadicTuning.sourceRate C1 hC1 p +
            TuningSourceDimensions.W C1 p *
              SourceDyadicTuning.sourceRate C1 hC1 p * (p.T : ℝ)) := hCombined
        _ ≤ 2 * (3 * Real.sqrt (3 * C1) *
              PublicGridConcentration.rowConcentrationScale p) :=
          mul_le_mul_of_nonneg_left hObjective (by norm_num)
        _ = 6 * Real.sqrt (3 * C1) *
            PublicGridConcentration.rowConcentrationScale p := by ring
    have hError :
        (p.m : ℝ) * (p.T : ℝ) *
            (5 / (N p : ℝ) ^ 2 + 2 / (N p : ℝ) ^ 2 +
              1 / (B_boot p : ℝ)) ≤
          7 + PublicGridConcentration.rowConcentrationScale p := by
      have hFalse :
          (p.m : ℝ) * (p.T : ℝ) * (1 / (B_boot p : ℝ)) ≤
            PublicGridConcentration.rowConcentrationScale p := by
        have hBlock := m_mul_T_div_B_boot_le_root_scale p
        have hb1 : 1 ≤ (b_N p : ℝ) := by
          exact_mod_cast Nat.succ_le_of_lt (ConstructorDimensions.b_N_pos p)
        have hBaseNonneg :
            0 ≤ (p.m : ℝ) * Real.sqrt (p.m : ℝ) *
              Real.sqrt ((p.K : ℝ) * (p.T : ℝ)) := by
          positivity
        calc
          (p.m : ℝ) * (p.T : ℝ) * (1 / (B_boot p : ℝ)) =
              (p.m : ℝ) * (p.T : ℝ) / (B_boot p : ℝ) := by ring
          _ ≤ (p.m : ℝ) * Real.sqrt (p.m : ℝ) *
              Real.sqrt ((p.K : ℝ) * (p.T : ℝ)) := hBlock
          _ ≤ PublicGridConcentration.rowConcentrationScale p := by
            calc
              _ ≤ ((p.m : ℝ) * Real.sqrt (p.m : ℝ) *
                  Real.sqrt ((p.K : ℝ) * (p.T : ℝ))) * (b_N p : ℝ) :=
                by
                  simpa only [mul_one] using
                    mul_le_mul_of_nonneg_left hb1 hBaseNonneg
              _ = PublicGridConcentration.rowConcentrationScale p := by rfl
      have hSeven := m_mul_T_mul_seven_div_N_sq_le_seven p
      have hSplit :
          (p.m : ℝ) * (p.T : ℝ) *
              (5 / (N p : ℝ) ^ 2 + 2 / (N p : ℝ) ^ 2 +
                1 / (B_boot p : ℝ)) =
            (p.m : ℝ) * (p.T : ℝ) * (7 / (N p : ℝ) ^ 2) +
              (p.m : ℝ) * (p.T : ℝ) * (1 / (B_boot p : ℝ)) := by
        ring
      rw [hSplit]
      exact add_le_add hSeven hFalse
    have hRound := m_mul_T_div_D_le_one p
    have hQge : 1 ≤ BootstrapStartupCostScale.Q_boot p := by
      have hScaleOne := SmallRegimeAbsorption.one_le_rowConcentrationScale p
      have hbOne : 1 ≤ (b_N p : ℝ) := by
        exact_mod_cast Nat.succ_le_of_lt (ConstructorDimensions.b_N_pos p)
      have hScale0 := PublicGridConcentration.rowConcentrationScale_nonneg p
      calc
        1 ≤ PublicGridConcentration.rowConcentrationScale p := hScaleOne
        _ ≤ PublicGridConcentration.rowConcentrationScale p * (b_N p : ℝ) :=
          by
            simpa only [mul_one] using
              mul_le_mul_of_nonneg_left hbOne hScale0
        _ = BootstrapStartupCostScale.Q_boot p :=
          (BootstrapStartupCostScale.Q_boot_eq_rowConcentrationScale_mul_b_N p).symm
    have hComponentSum :
        BootstrapStartupCostScale.Q_boot p +
            (p.m : ℝ) * (p.K : ℝ) * (b_N p : ℝ) +
            PublicGridConcentration.rowConcentrationScale p +
            ((TuningSourceDimensions.J p : ℝ) /
                SourceDyadicTuning.sourceRate C1 hC1 p +
              TuningSourceDimensions.W C1 p *
                SourceDyadicTuning.sourceRate C1 hC1 p * (p.T : ℝ)) +
            (p.m : ℝ) * (p.T : ℝ) /
              (SourceDyadicTuning.sourceRate C1 hC1 p * (D p : ℝ)) +
            (p.m : ℝ) * (p.T : ℝ) *
              (5 / (N p : ℝ) ^ 2 + 2 / (N p : ℝ) ^ 2 +
                1 / (B_boot p : ℝ)) +
            (p.m : ℝ) * (p.T : ℝ) / (D p : ℝ) ≤
          BootstrapStartupCostScale.Q_boot p +
            BootstrapStartupCostScale.Q_boot p +
            PublicGridConcentration.rowConcentrationScale p +
            6 * Real.sqrt (3 * C1) *
              PublicGridConcentration.rowConcentrationScale p +
            7 + PublicGridConcentration.rowConcentrationScale p + 1 := by
      nlinarith only [
        m_mul_K_mul_b_N_le_Q_boot_of_construction_branch Cb
          (le_trans (le_max_left _ _) hCbMax) p hbranch,
        hObjectiveAndPenalty, hError, hRound]
    have hScaleWeighted :
        (2 + 6 * Real.sqrt (3 * C1)) *
            PublicGridConcentration.rowConcentrationScale p ≤
          (2 + 6 * Real.sqrt (3 * C1)) *
            BootstrapStartupCostScale.Q_boot p :=
      mul_le_mul_of_nonneg_left
        (rowConcentrationScale_le_Q_boot p) (by positivity)
    have hEight : 8 ≤ 8 * BootstrapStartupCostScale.Q_boot p := by
      calc
        8 = 8 * 1 := by norm_num
        _ ≤ 8 * BootstrapStartupCostScale.Q_boot p :=
          mul_le_mul_of_nonneg_left hQge (by norm_num)
    have hCoefficientBound :
        BootstrapStartupCostScale.Q_boot p +
            BootstrapStartupCostScale.Q_boot p +
            PublicGridConcentration.rowConcentrationScale p +
            6 * Real.sqrt (3 * C1) *
              PublicGridConcentration.rowConcentrationScale p +
            7 + PublicGridConcentration.rowConcentrationScale p + 1 ≤
          (12 + 6 * Real.sqrt (3 * C1)) *
            BootstrapStartupCostScale.Q_boot p := by
      calc
        _ = 2 * BootstrapStartupCostScale.Q_boot p +
              (2 + 6 * Real.sqrt (3 * C1)) *
                PublicGridConcentration.rowConcentrationScale p + 8 := by ring
        _ ≤ 2 * BootstrapStartupCostScale.Q_boot p +
              (2 + 6 * Real.sqrt (3 * C1)) *
                BootstrapStartupCostScale.Q_boot p + 8 := by
          nlinarith only [hScaleWeighted]
        _ ≤ 2 * BootstrapStartupCostScale.Q_boot p +
              (2 + 6 * Real.sqrt (3 * C1)) *
                BootstrapStartupCostScale.Q_boot p +
              8 * BootstrapStartupCostScale.Q_boot p := by
          nlinarith only [hEight]
        _ = (12 + 6 * Real.sqrt (3 * C1)) *
            BootstrapStartupCostScale.Q_boot p := by ring
    refine ⟨m_mul_K_mul_b_N_le_Q_boot_of_construction_branch Cb
        (le_trans (le_max_left _ _) hCbMax) p hbranch,
      rowConcentrationScale_le_Q_boot p,
      m_mul_T_div_B_boot_le_root_scale p,
      m_mul_T_mul_seven_div_N_sq_le_seven p,
      hRound, ?_⟩
    unfold tunedNumericalRemainder
    calc
      _ = BootstrapStartupCostScale.Q_boot p +
            (p.m : ℝ) * (p.K : ℝ) * (b_N p : ℝ) +
            PublicGridConcentration.rowConcentrationScale p +
            ((TuningSourceDimensions.J p : ℝ) /
                SourceDyadicTuning.sourceRate C1 hC1 p +
              TuningSourceDimensions.W C1 p *
                SourceDyadicTuning.sourceRate C1 hC1 p * (p.T : ℝ)) +
            (p.m : ℝ) * (p.T : ℝ) /
              (SourceDyadicTuning.sourceRate C1 hC1 p * (D p : ℝ)) +
            (p.m : ℝ) * (p.T : ℝ) *
              (5 / (N p : ℝ) ^ 2 + 2 / (N p : ℝ) ^ 2 +
                1 / (B_boot p : ℝ)) +
            (p.m : ℝ) * (p.T : ℝ) / (D p : ℝ) := by ring
      _ ≤ _ := hComponentSum
      _ ≤ _ := hCoefficientBound

end Bandits.Support.TunedNumericalRemainder

end
