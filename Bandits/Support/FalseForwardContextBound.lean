/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Bandits Lean Project
-/
module

public import Bandits.Support.ConstructorDimensions
public import Bandits.Support.BootstrapDimensions
public import Bandits.Support.FalseRowSliceFactorization
public import Bandits.Support.FinitePublicationUnion

import Bandits.Support.FalseForwardContextUnion
import Bandits.Support.ForwardPrefixRareTail
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Fintype.BigOperators
import Mathlib.MeasureTheory.Measure.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Finite false-forward source contexts and their numerical union budget

The context carrier retains each block's actual possibly shortened calendar
subtype and all binary support/avoidance vectors on that subtype.  The
numerical union estimate is conditional on the source construction branch;
the generic event-family corollary leaves every individual rare-tail bound as
an explicit premise.

Sources: `sources/zip4/manuscript/appendix_b_communication.tex:350-357` and
`sources/zip4/manuscript/07_public_setup.tex:5-25`.
-/

public section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.FalseRowSliceFactorization
open MeasureTheory
open scoped ENNReal

namespace Bandits.Support.FalseForwardContextBound

/-- A source context `(s,J,i,a,z,x_a,x_z)`, with the two Boolean vectors on
the actual finite subtype of the possibly shortened block `s`.
Source: `appendix_b_communication.tex:350-357`. -/
@[expose] def Context (p : Parameters) : Type :=
  Σ s : Fin (n_boot p),
    Fin (M p) × Fin (p.m - 1) × Fin p.K × Fin p.K ×
      (BlockTime p s → Bool) × (BlockTime p s → Bool)

/-- Finiteness of the dependent source context carrier. -/
noncomputable instance contextFintype (p : Parameters) : Fintype (Context p) := by
  classical
  unfold Context
  exact Sigma.instFintype

/-- The cardinality of the dependent source context family, with the actual
block length in each summand. -/
theorem context_card_eq_sum (p : Parameters) :
    Fintype.card (Context p) =
      ∑ s : Fin (n_boot p),
        M p * (p.m - 1) * p.K ^ 2 *
          2 ^ (2 * Fintype.card (BlockTime p s)) := by
  classical
  unfold Context
  rw [Fintype.card_sigma]
  simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_fun,
    Fintype.card_bool]
  apply Finset.sum_congr rfl
  intro s hs
  rw [← pow_add, Nat.two_mul]
  ring

/-- `BlockTime` is exactly the subtype of the source calendar block, so its
cardinality records the shortened final block without a second calendar. -/
theorem blockTime_card_eq_calendarBlock_card (p : Parameters)
    (s : Fin (n_boot p)) :
    Fintype.card (BlockTime p s) = (calendarBlock p s).card := by
  classical
  simp [BlockTime]

/-- The exact dependent cardinal is bounded by the source coordinate count
times the maximum number of support/avoidance vector pairs. -/
theorem context_card_le_coordinate_budget (p : Parameters) :
    Fintype.card (Context p) ≤
      n_boot p * M p * (p.m - 1) * p.K ^ 2 * 2 ^ (2 * B_boot p) := by
  classical
  rw [context_card_eq_sum]
  calc
    _ ≤ ∑ s : Fin (n_boot p),
        M p * (p.m - 1) * p.K ^ 2 * 2 ^ (2 * B_boot p) := by
      apply Finset.sum_le_sum
      intro s hs
      have hblock : Fintype.card (BlockTime p s) ≤ B_boot p := by
        rw [blockTime_card_eq_calendarBlock_card]
        exact calendarBlock_card_le_B_boot p s
      have hpow :
          2 ^ (2 * Fintype.card (BlockTime p s)) ≤ 2 ^ (2 * B_boot p) := by
        apply Nat.pow_le_pow_right (by decide)
        exact Nat.mul_le_mul_left 2 hblock
      exact Nat.mul_le_mul_left (M p * (p.m - 1) * p.K ^ 2) hpow
    _ = n_boot p * M p * (p.m - 1) * p.K ^ 2 *
          2 ^ (2 * B_boot p) := by
      simp
      ring

private theorem T_le_N (p : Parameters) : p.T ≤ N p := by
  calc
    p.T ≤ 2 * p.T := by omega
    _ ≤ N p := ForwardPrefixRareTail.two_mul_T_le_N p

/-- The actual source coordinate factors are at most `N^6`.  The row factor
uses the accepted bound for the literal ceiling definition of `M`. -/
theorem context_coordinate_count_le_N_six (p : Parameters) :
    n_boot p * M p * (p.m - 1) * p.K ^ 2 ≤ N p ^ 6 := by
  have hblocks : n_boot p ≤ N p :=
    (n_boot_le_T p).trans (T_le_N p)
  have hrows : M p ≤ N p ^ 2 := FalseForwardContextUnion.M_le_N_sq p
  have hplayers : p.m - 1 ≤ N p :=
    (Nat.sub_le p.m 1).trans
      ((Nat.le_of_lt p.m_lt_K).trans (ConstructorDimensions.K_le_N p))
  have harms : p.K ≤ N p := ConstructorDimensions.K_le_N p
  have harmsSq : p.K ^ 2 ≤ N p ^ 2 := by
    simpa only [pow_two] using Nat.mul_le_mul harms harms
  have hprod₁ : n_boot p * M p ≤ N p * N p ^ 2 :=
    Nat.mul_le_mul hblocks hrows
  have hprod₂ : n_boot p * M p * (p.m - 1) ≤
      (N p * N p ^ 2) * N p := Nat.mul_le_mul hprod₁ hplayers
  have hprod₃ : n_boot p * M p * (p.m - 1) * p.K ^ 2 ≤
      ((N p * N p ^ 2) * N p) * N p ^ 2 := Nat.mul_le_mul hprod₂ harmsSq
  calc
    n_boot p * M p * (p.m - 1) * p.K ^ 2 ≤
        ((N p * N p ^ 2) * N p) * N p ^ 2 := hprod₃
    _ = N p ^ 6 := by ring

/-- The finite source context count is at most `N^6 2^(2 B_boot)`. -/
theorem context_card_le_N_six_mul_block_budget (p : Parameters) :
    Fintype.card (Context p) ≤ N p ^ 6 * 2 ^ (2 * B_boot p) := by
  calc
    Fintype.card (Context p) ≤
        n_boot p * M p * (p.m - 1) * p.K ^ 2 * 2 ^ (2 * B_boot p) :=
      context_card_le_coordinate_budget p
    _ ≤ N p ^ 6 * 2 ^ (2 * B_boot p) :=
      Nat.mul_le_mul_right _ (context_coordinate_count_le_N_six p)

/-- The literal construction-branch inequality implies the source block bound
`4 b_N ≤ B_boot`.  The strict numerical premise is exactly the branch scale
from `07_public_setup.tex:5-16` with the accepted source parameters. -/
theorem four_mul_b_N_le_B_boot_of_construction_branch (p : Parameters)
    (hbranch :
      (16 : ℝ) * (p.m : ℝ) * (p.K : ℝ) * (b_N p : ℝ) ^ 2 < (p.T : ℝ)) :
    4 * b_N p ≤ B_boot p := by
  have hmKpos : 0 < (p.m : ℝ) * (p.K : ℝ) :=
    mul_pos (Nat.cast_pos.mpr (ConstructorDimensions.m_pos p))
      (Nat.cast_pos.mpr (ConstructorDimensions.K_pos p))
  have hscaled :
      (16 : ℝ) * ((p.m : ℝ) * (p.K : ℝ)) * (b_N p : ℝ) ^ 2 < (p.T : ℝ) := by
    nlinarith [hbranch]
  have hratio :
      (4 * (b_N p : ℝ)) ^ 2 <
        (p.T : ℝ) / ((p.m : ℝ) * (p.K : ℝ)) := by
    apply (lt_div_iff₀ hmKpos).2
    nlinarith [hscaled]
  have hsqrt :
      4 * (b_N p : ℝ) ≤
        Real.sqrt ((p.T : ℝ) / ((p.m : ℝ) * (p.K : ℝ))) :=
    Real.le_sqrt_of_sq_le hratio.le
  have hB : 4 * (b_N p : ℝ) ≤ (B_boot p : ℝ) :=
    hsqrt.trans (B_boot_real_lower_bound p)
  exact_mod_cast hB

private theorem log_N_le_seven_tenths_b_N (p : Parameters) :
    Real.log (N p : ℝ) ≤ (7 / 10 : ℝ) * (b_N p : ℝ) := by
  have hNpos : 0 < (N p : ℝ) :=
    Nat.cast_pos.mpr (ConstructorDimensions.N_pos p)
  have hND : (N p : ℝ) < (D p : ℝ) := by
    exact_mod_cast ConstructorDimensions.N_lt_D p
  have hlogD : Real.log (D p : ℝ) =
      (b_N p : ℝ) * Real.log 2 := by
    rw [ConstructorDimensions.D, Nat.cast_pow, Real.log_pow, Nat.cast_ofNat]
  have hlog2 : Real.log 2 ≤ (7 / 10 : ℝ) := by
    exact le_of_lt (lt_trans Real.log_two_lt_d9 (by norm_num))
  calc
    Real.log (N p : ℝ) ≤ Real.log (D p : ℝ) :=
      (Real.log_lt_log hNpos hND).le
    _ = (b_N p : ℝ) * Real.log 2 := hlogD
    _ ≤ (7 / 10 : ℝ) * (b_N p : ℝ) := by
      calc
        (b_N p : ℝ) * Real.log 2 ≤
            (b_N p : ℝ) * (7 / 10 : ℝ) :=
          mul_le_mul_of_nonneg_left hlog2 (Nat.cast_nonneg _)
        _ = (7 / 10 : ℝ) * (b_N p : ℝ) := by ring

/-- The source exponential budget assuming only the proved block lower bound.
The branch-specialized theorem below constructs this premise internally. -/
theorem source_exponential_budget_of_block_lower_bound (p : Parameters)
    (hB : 4 * b_N p ≤ B_boot p) :
    (N p : ℝ) ^ 6 * (2 : ℝ) ^ (2 * B_boot p) *
        Real.exp (-((5 : ℝ) / 2) *
          ((B_boot p : ℝ) + (b_N p : ℝ))) ≤ 1 / (N p : ℝ) := by
  have hBreal : 4 * (b_N p : ℝ) ≤ (B_boot p : ℝ) := by
    exact_mod_cast hB
  have hlog2 : Real.log 2 ≤ (7 : ℝ) / 10 := by
    exact le_of_lt (lt_trans Real.log_two_lt_d9 (by norm_num))
  have hlogN := log_N_le_seven_tenths_b_N p
  have hBterm :
      (2 * (B_boot p : ℝ)) * Real.log 2 ≤
        (2 * (B_boot p : ℝ)) * ((7 : ℝ) / 10) :=
    mul_le_mul_of_nonneg_left hlog2 (by positivity)
  have hNterm :
      7 * Real.log (N p : ℝ) ≤
        (7 * (b_N p : ℝ)) * ((7 : ℝ) / 10) := by
    calc
      7 * Real.log (N p : ℝ) ≤
          7 * ((7 / 10 : ℝ) * (b_N p : ℝ)) :=
        mul_le_mul_of_nonneg_left hlogN (by norm_num)
      _ = (7 * (b_N p : ℝ)) * ((7 : ℝ) / 10) := by ring
  have hlinear :
      (2 * (B_boot p : ℝ)) * ((7 : ℝ) / 10) +
          (7 * (b_N p : ℝ)) * ((7 : ℝ) / 10) ≤
        ((5 : ℝ) / 2) * ((B_boot p : ℝ) + (b_N p : ℝ)) := by
    nlinarith [hBreal]
  have hlogBudget :
      7 * Real.log (N p : ℝ) +
          (2 * (B_boot p : ℝ)) * Real.log 2 ≤
        ((5 : ℝ) / 2) * ((B_boot p : ℝ) + (b_N p : ℝ)) := by
    linarith [hNterm, hBterm, hlinear]
  have hproductPos :
      0 < (N p : ℝ) ^ 7 * (2 : ℝ) ^ (2 * B_boot p) :=
    mul_pos (pow_pos (Nat.cast_pos.mpr (ConstructorDimensions.N_pos p)) _)
      (pow_pos (by norm_num : (0 : ℝ) < 2) _)
  have hlogProduct :
      Real.log ((N p : ℝ) ^ 7 * (2 : ℝ) ^ (2 * B_boot p)) =
        7 * Real.log (N p : ℝ) +
          (2 * (B_boot p : ℝ)) * Real.log 2 := by
    rw [Real.log_mul (pow_ne_zero _
        (Nat.cast_ne_zero.mpr (Nat.ne_of_gt (ConstructorDimensions.N_pos p))))
        (pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0)),
      Real.log_pow, Real.log_pow]
    norm_num [mul_comm]
  have hpowered :
      (N p : ℝ) ^ 7 * (2 : ℝ) ^ (2 * B_boot p) ≤
        Real.exp (((5 : ℝ) / 2) *
          ((B_boot p : ℝ) + (b_N p : ℝ))) :=
    (Real.log_le_iff_le_exp hproductPos).1 (hlogProduct ▸ hlogBudget)
  have hcancel :
      ((N p : ℝ) ^ 6 * (2 : ℝ) ^ (2 * B_boot p) *
          Real.exp (-((5 : ℝ) / 2) *
            ((B_boot p : ℝ) + (b_N p : ℝ)))) * (N p : ℝ) ≤ 1 := by
    calc
      _ = ((N p : ℝ) ^ 7 * (2 : ℝ) ^ (2 * B_boot p)) *
          Real.exp (-((5 : ℝ) / 2) *
            ((B_boot p : ℝ) + (b_N p : ℝ))) := by ring
      _ ≤ Real.exp (((5 : ℝ) / 2) *
            ((B_boot p : ℝ) + (b_N p : ℝ))) *
          Real.exp (-((5 : ℝ) / 2) *
            ((B_boot p : ℝ) + (b_N p : ℝ))) :=
        mul_le_mul_of_nonneg_right hpowered (Real.exp_nonneg _)
      _ = 1 := by
        rw [← Real.exp_add]
        have harg :
            ((5 : ℝ) / 2) * ((B_boot p : ℝ) + (b_N p : ℝ)) +
                (-((5 : ℝ) / 2)) *
                  ((B_boot p : ℝ) + (b_N p : ℝ)) = 0 := by ring
        rw [harg, Real.exp_zero]
  exact (le_div_iff₀
    (Nat.cast_pos.mpr (ConstructorDimensions.N_pos p))).2 hcancel

/-- The source exponential budget under the genuine numerical construction
branch.  The conclusion does not assume `4 b_N ≤ B_boot`; that inequality is
proved from the branch in the proof. -/
theorem source_exponential_budget_of_construction_branch (p : Parameters)
    (hbranch :
      (16 : ℝ) * (p.m : ℝ) * (p.K : ℝ) * (b_N p : ℝ) ^ 2 < (p.T : ℝ)) :
    (N p : ℝ) ^ 6 * (2 : ℝ) ^ (2 * B_boot p) *
        Real.exp (-((5 : ℝ) / 2) *
          ((B_boot p : ℝ) + (b_N p : ℝ))) ≤ 1 / (N p : ℝ) :=
  source_exponential_budget_of_block_lower_bound p
    (four_mul_b_N_le_B_boot_of_construction_branch p hbranch)

/-- The union of supplied bad events indexed by the literal finite source
context carrier. -/
@[expose] def suppliedContextBadUnion {Ω : Type*} (p : Parameters)
    (bad : Context p → Set Ω) : Set Ω :=
  ⋃ c, bad c

/-- Every measurable supplied context event gives a measurable finite union. -/
theorem measurableSet_suppliedContextBadUnion {Ω : Type*}
    [MeasurableSpace Ω] (p : Parameters) (bad : Context p → Set Ω)
    (hmeas : ∀ c, MeasurableSet (bad c)) :
    MeasurableSet (suppliedContextBadUnion p bad) := by
  simpa [suppliedContextBadUnion] using MeasurableSet.iUnion hmeas

/-- Generic finite-family corollary: if each supplied context event has the
fixed-context rare-tail probability, then their union has loss at most `1/N`.
The event family and every per-event probability estimate remain explicit
inputs; this theorem does not identify the union with the manuscript's common
public event or establish a physical false-forward probability bound. -/
theorem suppliedContextBadUnion_probability_le_inv_N (p : Parameters)
    (hbranch :
      (16 : ℝ) * (p.m : ℝ) * (p.K : ℝ) * (b_N p : ℝ) ^ 2 < (p.T : ℝ))
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (bad : Context p → Set Ω)
    (hmeas : ∀ c, MeasurableSet (bad c))
    (hprob : ∀ c, μ (bad c) ≤ ENNReal.ofReal
      (Real.exp (-((5 : ℝ) / 2) *
        ((B_boot p : ℝ) + (b_N p : ℝ))))) :
    MeasurableSet (suppliedContextBadUnion p bad) ∧
      μ (suppliedContextBadUnion p bad) ≤
        ENNReal.ofReal (1 / (N p : ℝ)) := by
  constructor
  · exact measurableSet_suppliedContextBadUnion p bad hmeas
  · have hunion := FinitePublicationUnion.finiteTypeUnionBound μ bad
      (ENNReal.ofReal
        (Real.exp (-((5 : ℝ) / 2) *
          ((B_boot p : ℝ) + (b_N p : ℝ))))) hprob
    have hcount := context_card_le_N_six_mul_block_budget p
    have hcountENN :
        (Fintype.card (Context p) : ℝ≥0∞) ≤
          ((N p ^ 6 * 2 ^ (2 * B_boot p) : ℕ) : ℝ≥0∞) := by
      exact_mod_cast hcount
    calc
      μ (suppliedContextBadUnion p bad) ≤
          (Fintype.card (Context p) : ℝ≥0∞) *
            ENNReal.ofReal
              (Real.exp (-((5 : ℝ) / 2) *
                ((B_boot p : ℝ) + (b_N p : ℝ)))) := by
        simpa [suppliedContextBadUnion,
          FinitePublicationUnion.badEvent] using hunion
      _ ≤ ((N p ^ 6 * 2 ^ (2 * B_boot p) : ℕ) : ℝ≥0∞) *
            ENNReal.ofReal
              (Real.exp (-((5 : ℝ) / 2) *
                ((B_boot p : ℝ) + (b_N p : ℝ)))) :=
        mul_le_mul_of_nonneg_right hcountENN bot_le
      _ = ENNReal.ofReal
            ((N p : ℝ) ^ 6 * (2 : ℝ) ^ (2 * B_boot p) *
              Real.exp (-((5 : ℝ) / 2) *
                ((B_boot p : ℝ) + (b_N p : ℝ)))) := by
        rw [← ENNReal.ofReal_natCast, Nat.cast_mul, Nat.cast_pow,
          Nat.cast_pow, Nat.cast_ofNat,
          ← ENNReal.ofReal_mul (by positivity)]
      _ ≤ ENNReal.ofReal (1 / (N p : ℝ)) :=
        ENNReal.ofReal_le_ofReal
          (source_exponential_budget_of_construction_branch p hbranch)

end Bandits.Support.FalseForwardContextBound

end
