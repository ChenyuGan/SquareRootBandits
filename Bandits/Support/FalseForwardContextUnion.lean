/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.BootstrapDimensions
public import Bandits.Support.ConstructorDimensions
public import Bandits.Support.FinitePublicationUnion

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Finite local contexts for false forward tests

This module counts the literal local contexts used by the source's false-row
forward-test argument and proves its numerical finite-union budget.  It does
not define the full test event, prove an individual rare-tail estimate, or
identify arbitrary supplied histories with physical executions.

Sources: `sources/zip4/manuscript/appendix_b_communication.tex:302-357`,
`sources/zip4/manuscript/07_public_setup.tex:13-25`, and
`sources/zip4/manuscript/08_main_theorem.tex:4-24`.
-/

public section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open MeasureTheory
open scoped ENNReal

namespace Bandits.Support.FalseForwardContextUnion

/-- The actual finite subtype of zero-based calendar rounds in block `s`.
Its size depends on `s`, so context slices use this dependent type rather than
all horizon coordinates. -/
abbrev BlockRound (p : Parameters) (s : Fin (n_boot p)) : Type :=
  {t : Fin p.T // t ∈ calendarBlock p s}

/-- The fixed-block context coordinates, with both Boolean functions still
living on that block's actual finite subtype. -/
abbrev BlockChoices (p : Parameters) (s : Fin (n_boot p)) : Type :=
  Fin (M p) × Fin (p.m - 1) × Fin p.K × Fin p.K ×
    (BlockRound p s → Bool) × (BlockRound p s → Bool)

noncomputable instance blockRoundFintype (p : Parameters) (s : Fin (n_boot p)) :
    Fintype (BlockRound p s) := by
  classical
  unfold BlockRound
  infer_instance

noncomputable instance blockSliceFintype (p : Parameters) (s : Fin (n_boot p)) :
    Fintype (BlockRound p s → Bool) := by
  classical
  exact Pi.instFintype

/-- The manuscript's local context `(s,J,i,a,z,x_a,x_z)`.  The two Boolean
slices are functions on the actual subtype of `calendarBlock p s`; in
particular, the shortened final block has its own shorter function domain. -/
abbrev LocalContext (p : Parameters) : Type :=
  Σ s : Fin (n_boot p), BlockChoices p s

noncomputable instance localContextFintype (p : Parameters) : Fintype (LocalContext p) := by
  classical
  unfold LocalContext
  exact Sigma.instFintype

/-- The source's one-based label for a Lean `Fin n` index. -/
@[expose] def sourceIndexLabel {n : ℕ} (i : Fin n) : ℕ := i.val + 1

/-- Every Lean index labels an element of the source range `[n]`. -/
theorem sourceIndexLabel_mem_range {n : ℕ} (i : Fin n) :
    1 ≤ sourceIndexLabel i ∧ sourceIndexLabel i ≤ n := by
  constructor
  · simp [sourceIndexLabel]
  · exact Nat.succ_le_of_lt i.isLt

/-- The zero-based-to-one-based label map is injective. -/
theorem sourceIndexLabel_injective {n : ℕ} {i j : Fin n}
    (h : sourceIndexLabel i = sourceIndexLabel j) : i = j := by
  apply Fin.ext
  simpa [sourceIndexLabel] using h

/-- Every valid one-based source label is represented by exactly one `Fin n`
index (existence here, together with `sourceIndexLabel_injective`). -/
theorem sourceIndexLabel_surjective {n j : ℕ} (hj : 1 ≤ j ∧ j ≤ n) :
    ∃ i : Fin n, sourceIndexLabel i = j := by
  refine ⟨⟨j - 1, by omega⟩, ?_⟩
  simp [sourceIndexLabel]
  omega

/-- The actual block subtype corresponds exactly to the manuscript's
one-based block interval: for block label `S = s.val + 1`, its rounds are
`(S - 1) B_boot + 1` through `min(T, S B_boot)`. -/
theorem sourceBlockRound_label_mem (p : Parameters) (s : Fin (n_boot p))
    (t : BlockRound p s) :
    (sourceIndexLabel s - 1) * B_boot p + 1 ≤
        BootstrapDimensions.manuscriptRound p t.1 ∧
      BootstrapDimensions.manuscriptRound p t.1 ≤
        min p.T (sourceIndexLabel s * B_boot p) := by
  have hsource : sourceIndexLabel s - 1 = s.val := by
    simp [sourceIndexLabel]
  rw [hsource]
  have hmem := (mem_calendarBlock_iff p s t.1).mp t.2
  simp only [sourceIndexLabel, BootstrapDimensions.manuscriptRound]
  exact ⟨by omega, by omega⟩

/-- Every one-based round in the source block interval comes from a member of
`BlockRound p s`. -/
theorem sourceBlockRound_label_surjective (p : Parameters) (s : Fin (n_boot p))
    (r : ℕ)
    (hr : (sourceIndexLabel s - 1) * B_boot p + 1 ≤ r ∧
      r ≤ min p.T (sourceIndexLabel s * B_boot p)) :
    ∃ t : BlockRound p s, BootstrapDimensions.manuscriptRound p t.1 = r := by
  have hsource : sourceIndexLabel s - 1 = s.val := by
    simp [sourceIndexLabel]
  have hlo : s.val * B_boot p + 1 ≤ r := by
    simpa only [hsource] using hr.1
  have hhi : r ≤ min p.T ((s.val + 1) * B_boot p) := by
    simpa [sourceIndexLabel] using hr.2
  have hround_le : r - 1 < p.T := by
    have hle := hhi.trans (Nat.min_le_left p.T ((s.val + 1) * B_boot p))
    omega
  let t₀ : Fin p.T := ⟨r - 1, hround_le⟩
  have hblock : t₀ ∈ calendarBlock p s := by
    rw [mem_calendarBlock_iff_manuscriptRound]
    have hlabel : BootstrapDimensions.manuscriptRound p t₀ = r := by
      simp only [BootstrapDimensions.manuscriptRound]
      dsimp [t₀]
      omega
    rw [hlabel]
    exact ⟨hlo, hhi⟩
  refine ⟨⟨t₀, hblock⟩, ?_⟩
  simp only [BootstrapDimensions.manuscriptRound]
  dsimp [t₀]
  omega

/-- The one-based source round label is injective on the actual block subtype. -/
theorem sourceBlockRound_label_injective (p : Parameters) (s : Fin (n_boot p))
    {t u : BlockRound p s}
    (h : BootstrapDimensions.manuscriptRound p t.1 =
      BootstrapDimensions.manuscriptRound p u.1) :
    t = u := by
  apply Subtype.ext
  apply Fin.ext
  simp only [BootstrapDimensions.manuscriptRound] at h
  omega

/-- Exact cardinal sum for the dependent source context family.  The exponent
uses the size of each individual calendar block. -/
theorem localContext_card_eq_sum (p : Parameters) :
    Fintype.card (LocalContext p) =
      ∑ s : Fin (n_boot p),
        M p * (p.m - 1) * p.K ^ 2 * 2 ^ (2 * (calendarBlock p s).card) := by
  classical
  rw [Fintype.card_sigma]
  simp only [BlockChoices, Fintype.card_prod, Fintype.card_fin, Fintype.card_fun,
    Fintype.card_bool, Fintype.card_coe, Nat.two_mul, pow_add]
  apply Finset.sum_congr rfl
  intro s hs
  ring

/-- The source row count obeys `M ≤ N²`, derived from its literal ceiling
definition and the constructor dimensions. -/
theorem M_le_N_sq (p : Parameters) : M p ≤ N p ^ 2 := by
  have hm : 2 ≤ p.m := p.two_le_m
  have hb : 1 ≤ b_N p := Nat.succ_le_of_lt (ConstructorDimensions.b_N_pos p)
  have hdenNat : 2 * 1 ≤ p.m * b_N p := Nat.mul_le_mul hm hb
  have hden : (2 : ℝ) ≤ (p.m : ℝ) * (b_N p : ℝ) := by
    exact_mod_cast hdenNat
  have hdenpos : 0 < (p.m : ℝ) * (b_N p : ℝ) := by positivity
  have hrate :
      (8 : ℝ) * (p.T : ℝ) ^ 2 / ((p.m : ℝ) * (b_N p : ℝ)) ≤
        4 * (p.T : ℝ) ^ 2 := by
    apply (div_le_iff₀ hdenpos).2
    have hden' : (8 : ℝ) ≤ 4 * ((p.m : ℝ) * (b_N p : ℝ)) := by
      nlinarith
    calc
      (8 : ℝ) * (p.T : ℝ) ^ 2 ≤
          (4 * ((p.m : ℝ) * (b_N p : ℝ))) * (p.T : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right hden' (sq_nonneg _)
      _ = (4 * (p.T : ℝ) ^ 2) * ((p.m : ℝ) * (b_N p : ℝ)) := by ring
  have hMreal :
      (M p : ℝ) <
        (8 : ℝ) * (p.T : ℝ) ^ 2 / ((p.m : ℝ) * (b_N p : ℝ)) + 1 := by
    rw [ConstructorDimensions.M]
    exact Nat.ceil_lt_add_one (div_nonneg (by positivity) (by positivity))
  have hMreal' : (M p : ℝ) < ((4 * p.T ^ 2 + 1 : ℕ) : ℝ) := by
    calc
      (M p : ℝ) <
          (8 : ℝ) * (p.T : ℝ) ^ 2 / ((p.m : ℝ) * (b_N p : ℝ)) + 1 := hMreal
      _ ≤ 4 * (p.T : ℝ) ^ 2 + 1 := by linarith [hrate]
      _ = ((4 * p.T ^ 2 + 1 : ℕ) : ℝ) := by norm_num
  have hMnat : M p < 4 * p.T ^ 2 + 1 := by exact_mod_cast hMreal'
  have hMsmall : M p ≤ 4 * p.T ^ 2 := Nat.lt_succ_iff.mp hMnat
  have hK : 3 ≤ p.K := by
    exact Nat.succ_le_of_lt (lt_of_le_of_lt p.two_le_m p.m_lt_K)
  have hfactor : 12 ≤ 2 * p.K * p.m := by
    calc
      12 = (2 * 3) * 2 := by norm_num
      _ ≤ (2 * p.K) * 2 := Nat.mul_le_mul_right 2 (Nat.mul_le_mul_left 2 hK)
      _ ≤ (2 * p.K) * p.m := Nat.mul_le_mul_left (2 * p.K) p.two_le_m
  have hNlower : 12 * (p.T + 1) ≤ N p := by
    change 12 * (p.T + 1) ≤ (2 * p.K * p.m) * (p.T + 1)
    exact Nat.mul_le_mul_right (p.T + 1) hfactor
  have hTsq : p.T ^ 2 ≤ (p.T + 1) ^ 2 := by
    exact Nat.pow_le_pow_left (Nat.le_succ p.T) 2
  have hscaled : 4 * p.T ^ 2 ≤ (12 * (p.T + 1)) ^ 2 := by
    calc
      4 * p.T ^ 2 ≤ 4 * (p.T + 1) ^ 2 := Nat.mul_le_mul_left 4 hTsq
      _ ≤ 144 * (p.T + 1) ^ 2 := Nat.mul_le_mul_right _ (by omega)
      _ = (12 * (p.T + 1)) ^ 2 := by ring
  have hNpow : (12 * (p.T + 1)) ^ 2 ≤ N p ^ 2 := by
    simpa only [pow_two] using Nat.mul_le_mul hNlower hNlower
  exact hMsmall.trans (hscaled.trans hNpow)

/-- `T` is at most the literal constructor size `N`. -/
theorem T_le_N (p : Parameters) : p.T ≤ N p := by
  have hm : 1 ≤ p.m := Nat.succ_le_of_lt (ConstructorDimensions.m_pos p)
  have hK : 1 ≤ p.K := Nat.succ_le_of_lt (ConstructorDimensions.K_pos p)
  have h2K : 2 ≤ 2 * p.K := by
    simpa using Nat.mul_le_mul_left 2 hK
  have hfactor : 1 ≤ 2 * p.K * p.m := by
    calc
      1 ≤ 2 := by omega
      _ ≤ 2 * p.K := h2K
      _ ≤ (2 * p.K) * p.m := by
        simpa using Nat.mul_le_mul_left (2 * p.K) hm
  calc
    p.T ≤ p.T + 1 := Nat.le_succ p.T
    _ = 1 * (p.T + 1) := by simp
    _ ≤ (2 * p.K * p.m) * (p.T + 1) := Nat.mul_le_mul_right _ hfactor
    _ = N p := rfl

/-- No dimension-budget hypothesis is assumed: the literal factors satisfy
`n_boot * M * (m - 1) * K² ≤ N⁶`. -/
theorem context_coordinate_count_le_N_six (p : Parameters) :
    n_boot p * M p * (p.m - 1) * p.K ^ 2 ≤ N p ^ 6 := by
  have hblocks : n_boot p ≤ N p :=
    (n_boot_le_T p).trans (T_le_N p)
  have hrows : M p ≤ N p ^ 2 := M_le_N_sq p
  have hplayers : p.m - 1 ≤ N p :=
    (Nat.sub_le p.m 1).trans (Nat.le_trans (Nat.le_of_lt p.m_lt_K)
      (ConstructorDimensions.K_le_N p))
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

/-- The source cardinal sum is bounded by the number of coordinate tuples
times the maximum number of Boolean block-slice pairs. -/
theorem localContext_card_le_coordinate_budget (p : Parameters) :
    Fintype.card (LocalContext p) ≤
      n_boot p * M p * (p.m - 1) * p.K ^ 2 * 2 ^ (2 * B_boot p) := by
  classical
  rw [localContext_card_eq_sum]
  calc
    _ ≤ ∑ s : Fin (n_boot p),
        M p * (p.m - 1) * p.K ^ 2 * 2 ^ (2 * B_boot p) := by
      apply Finset.sum_le_sum
      intro s hs
      have hpow : 2 ^ (2 * (calendarBlock p s).card) ≤ 2 ^ (2 * B_boot p) := by
        apply Nat.pow_le_pow_right (by decide)
        exact Nat.mul_le_mul_left 2 (calendarBlock_card_le_B_boot p s)
      exact Nat.mul_le_mul_left (M p * (p.m - 1) * p.K ^ 2) hpow
    _ = n_boot p * M p * (p.m - 1) * p.K ^ 2 * 2 ^ (2 * B_boot p) := by
      simp
      ring

/-- The actual local-context cardinal is at most `N⁶ 2^(2 B_boot)`. -/
theorem localContext_card_le_N_six_mul_block_budget (p : Parameters) :
    Fintype.card (LocalContext p) ≤ N p ^ 6 * 2 ^ (2 * B_boot p) := by
  calc
    Fintype.card (LocalContext p) ≤
        n_boot p * M p * (p.m - 1) * p.K ^ 2 * 2 ^ (2 * B_boot p) :=
      localContext_card_le_coordinate_budget p
    _ ≤ N p ^ 6 * 2 ^ (2 * B_boot p) :=
      Nat.mul_le_mul_right _ (context_coordinate_count_le_N_six p)

/-- From the source large-horizon branch and `C_b ≥ 64`, the exact real square
root and ceiling definition gives the required `4 b_N ≤ B_boot`. -/
theorem four_mul_b_N_le_B_boot (C_b : ℝ) (hC_b : 64 ≤ C_b)
    (p : Parameters)
    (hbranch : C_b * ((p.m : ℝ) * (p.K : ℝ)) * (b_N p : ℝ) ^ 2 < (p.T : ℝ)) :
    4 * b_N p ≤ B_boot p := by
  have hmKpos : 0 < (p.m : ℝ) * (p.K : ℝ) :=
    mul_pos (Nat.cast_pos.mpr (ConstructorDimensions.m_pos p))
      (Nat.cast_pos.mpr (ConstructorDimensions.K_pos p))
  have hbnonneg : 0 ≤ (b_N p : ℝ) ^ 2 := sq_nonneg _
  have hscaled :
      (64 : ℝ) * ((p.m : ℝ) * (p.K : ℝ)) * (b_N p : ℝ) ^ 2 < (p.T : ℝ) := by
    calc
      (64 : ℝ) * ((p.m : ℝ) * (p.K : ℝ)) * (b_N p : ℝ) ^ 2 ≤
          C_b * ((p.m : ℝ) * (p.K : ℝ)) * (b_N p : ℝ) ^ 2 := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hC_b hmKpos.le) hbnonneg
      _ < (p.T : ℝ) := hbranch
  have hratio :
      (4 * (b_N p : ℝ)) ^ 2 < (p.T : ℝ) / ((p.m : ℝ) * (p.K : ℝ)) := by
    apply (lt_div_iff₀ hmKpos).2
    nlinarith [hscaled]
  have hsqrt :
      4 * (b_N p : ℝ) ≤
        Real.sqrt ((p.T : ℝ) / ((p.m : ℝ) * (p.K : ℝ))) := by
    exact Real.le_sqrt_of_sq_le hratio.le
  have hB : 4 * (b_N p : ℝ) ≤ (B_boot p : ℝ) :=
    hsqrt.trans (B_boot_real_lower_bound p)
  exact_mod_cast hB

/-- The source size has logarithm at most `b_N log 2`, proved from `N < D`.
The logarithm signs and the identity for the actual dyadic `D` are explicit. -/
theorem log_N_le_b_N_mul_log_two (p : Parameters) :
    Real.log (N p : ℝ) ≤ (b_N p : ℝ) * Real.log 2 := by
  have hNpos : 0 < (N p : ℝ) := Nat.cast_pos.mpr (ConstructorDimensions.N_pos p)
  have hND : (N p : ℝ) < (D p : ℝ) := by
    exact_mod_cast ConstructorDimensions.N_lt_D p
  have hlog : Real.log (N p : ℝ) < Real.log (D p : ℝ) :=
    Real.log_lt_log hNpos hND
  have hlogD : Real.log (D p : ℝ) = (b_N p : ℝ) * Real.log 2 := by
    rw [ConstructorDimensions.D, Nat.cast_pow, Real.log_pow, Nat.cast_ofNat]
  exact hlog.le.trans_eq hlogD

private theorem log_two_le_seven_tenths : Real.log 2 ≤ (7 : ℝ) / 10 := by
  exact Real.log_two_lt_d9.le.trans (by norm_num)

/-- Positivity of the natural logarithm of two. -/
theorem log_two_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)

/-- The source exponential budget, proved with no independently chosen
`N₀`.  The proof uses the true `N < D` logarithm estimate and the `B_boot`
ceiling bound derived from the branch. -/
theorem source_exponential_budget (C_b : ℝ) (hC_b : 64 ≤ C_b)
    (p : Parameters)
    (hbranch : C_b * ((p.m : ℝ) * (p.K : ℝ)) * (b_N p : ℝ) ^ 2 < (p.T : ℝ)) :
    (N p : ℝ) ^ 6 * (2 : ℝ) ^ (2 * B_boot p) *
        Real.exp (-((5 : ℝ) / 2) * ((B_boot p : ℝ) + (b_N p : ℝ))) ≤
      1 / (N p : ℝ) := by
  have hBnat := four_mul_b_N_le_B_boot C_b hC_b p hbranch
  have hB : 4 * (b_N p : ℝ) ≤ (B_boot p : ℝ) := by exact_mod_cast hBnat
  have hBnonneg : 0 ≤ (B_boot p : ℝ) := Nat.cast_nonneg _
  have hbnonneg : 0 ≤ (b_N p : ℝ) := Nat.cast_nonneg _
  have hlog2upper := log_two_le_seven_tenths
  have hlogN := log_N_le_b_N_mul_log_two p
  have hBterm :
      (2 * (B_boot p : ℝ)) * Real.log 2 ≤
        (2 * (B_boot p : ℝ)) * ((7 : ℝ) / 10) :=
    mul_le_mul_of_nonneg_left hlog2upper (by positivity)
  have hNterm :
      7 * Real.log (N p : ℝ) ≤
        (7 * (b_N p : ℝ)) * ((7 : ℝ) / 10) := by
    calc
      7 * Real.log (N p : ℝ) ≤ 7 * ((b_N p : ℝ) * Real.log 2) :=
        mul_le_mul_of_nonneg_left hlogN (by norm_num)
      _ = (7 * (b_N p : ℝ)) * Real.log 2 := by ring
      _ ≤ (7 * (b_N p : ℝ)) * ((7 : ℝ) / 10) :=
        mul_le_mul_of_nonneg_left hlog2upper (by positivity)
  have hlinear :
      (2 * (B_boot p : ℝ)) * ((7 : ℝ) / 10) +
          (7 * (b_N p : ℝ)) * ((7 : ℝ) / 10) ≤
        ((5 : ℝ) / 2) * ((B_boot p : ℝ) + (b_N p : ℝ)) := by
    nlinarith [hB]
  have hlogBudget :
      7 * Real.log (N p : ℝ) +
          (2 * (B_boot p : ℝ)) * Real.log 2 ≤
        ((5 : ℝ) / 2) * ((B_boot p : ℝ) + (b_N p : ℝ)) := by
    linarith [hNterm, hBterm, hlinear]
  have hproductPos :
      0 < (N p : ℝ) ^ 7 * (2 : ℝ) ^ (2 * B_boot p) := by
    exact mul_pos (pow_pos (Nat.cast_pos.mpr (ConstructorDimensions.N_pos p)) _)
      (pow_pos (by norm_num : (0 : ℝ) < 2) _)
  have hlogProduct :
      Real.log ((N p : ℝ) ^ 7 * (2 : ℝ) ^ (2 * B_boot p)) =
        7 * Real.log (N p : ℝ) + (2 * (B_boot p : ℝ)) * Real.log 2 := by
    rw [Real.log_mul (pow_ne_zero _ (Nat.cast_ne_zero.mpr
      (Nat.ne_of_gt (ConstructorDimensions.N_pos p))))
      (pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0)),
      Real.log_pow, Real.log_pow]
    norm_num [mul_comm]
  have hpowered :
      (N p : ℝ) ^ 7 * (2 : ℝ) ^ (2 * B_boot p) ≤
        Real.exp (((5 : ℝ) / 2) * ((B_boot p : ℝ) + (b_N p : ℝ))) := by
    exact (Real.log_le_iff_le_exp hproductPos).1
      (hlogProduct ▸ hlogBudget)
  have hcancel :
      ((N p : ℝ) ^ 6 * (2 : ℝ) ^ (2 * B_boot p) *
          Real.exp (-((5 : ℝ) / 2) * ((B_boot p : ℝ) + (b_N p : ℝ)))) *
          (N p : ℝ) ≤ 1 := by
    calc
      _ = ((N p : ℝ) ^ 7 * (2 : ℝ) ^ (2 * B_boot p)) *
          Real.exp (-((5 : ℝ) / 2) * ((B_boot p : ℝ) + (b_N p : ℝ))) := by
        ring
      _ ≤ Real.exp (((5 : ℝ) / 2) * ((B_boot p : ℝ) + (b_N p : ℝ))) *
          Real.exp (-((5 : ℝ) / 2) * ((B_boot p : ℝ) + (b_N p : ℝ))) :=
        mul_le_mul_of_nonneg_right hpowered (Real.exp_nonneg _)
      _ = 1 := by
        rw [← Real.exp_add]
        have harg :
            ((5 : ℝ) / 2) * ((B_boot p : ℝ) + (b_N p : ℝ)) +
                (-((5 : ℝ) / 2)) * ((B_boot p : ℝ) + (b_N p : ℝ)) = 0 := by ring
        rw [harg, Real.exp_zero]
  exact (le_div_iff₀ (Nat.cast_pos.mpr (ConstructorDimensions.N_pos p))).2 hcancel

/-- The finite union of supplied bad events indexed by literal local contexts.
This is a generic union object, not the manuscript's complete `G_test` event. -/
@[expose] def badContextUnion {Ω : Type*} (p : Parameters)
    (bad : LocalContext p → Set Ω) : Set Ω :=
  ⋃ c, bad c

/-- Measurability of the finite union follows from measurability of every
individual context event. -/
theorem measurableSet_badContextUnion {Ω : Type*} [MeasurableSpace Ω]
    (p : Parameters) (bad : LocalContext p → Set Ω)
    (hmeas : ∀ c, MeasurableSet (bad c)) :
    MeasurableSet (badContextUnion p bad) := by
  simpa [badContextUnion] using MeasurableSet.iUnion hmeas

/-- Conditional finite-union consumer for measurable context events.  Its
per-context tail bound is an explicit generic trust boundary; the result proves
only the numerical union budget and does not claim any source rare-tail,
independence, or physical-execution theorem. -/
theorem badContextUnion_probability_le_inv_N (C_b : ℝ) (hC_b : 64 ≤ C_b)
    (p : Parameters)
    (hbranch : C_b * ((p.m : ℝ) * (p.K : ℝ)) * (b_N p : ℝ) ^ 2 < (p.T : ℝ))
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (bad : LocalContext p → Set Ω)
    (hmeas : ∀ c, MeasurableSet (bad c))
    (hprob : ∀ c, μ (bad c) ≤ ENNReal.ofReal
      (Real.exp (-((5 : ℝ) / 2) * ((B_boot p : ℝ) + (b_N p : ℝ))))) :
    MeasurableSet (badContextUnion p bad) ∧
      μ (badContextUnion p bad) ≤ ENNReal.ofReal (1 / (N p : ℝ)) := by
  constructor
  · exact measurableSet_badContextUnion p bad hmeas
  · have hunion :=
      FinitePublicationUnion.finiteTypeUnionBound μ bad
        (ENNReal.ofReal
          (Real.exp (-((5 : ℝ) / 2) * ((B_boot p : ℝ) + (b_N p : ℝ)))))
        hprob
    have hcount := localContext_card_le_N_six_mul_block_budget p
    have hcountENN :
        (Fintype.card (LocalContext p) : ℝ≥0∞) ≤
          ((N p ^ 6 * 2 ^ (2 * B_boot p) : ℕ) : ℝ≥0∞) := by
      exact_mod_cast hcount
    calc
      μ (badContextUnion p bad) ≤
          (Fintype.card (LocalContext p) : ℝ≥0∞) *
            ENNReal.ofReal
              (Real.exp (-((5 : ℝ) / 2) * ((B_boot p : ℝ) + (b_N p : ℝ)))) := by
        simpa [badContextUnion, FinitePublicationUnion.badEvent] using hunion
      _ ≤ ((N p ^ 6 * 2 ^ (2 * B_boot p) : ℕ) : ℝ≥0∞) *
            ENNReal.ofReal
              (Real.exp (-((5 : ℝ) / 2) * ((B_boot p : ℝ) + (b_N p : ℝ)))) :=
        mul_le_mul_of_nonneg_right hcountENN bot_le
      _ = ENNReal.ofReal
            ((N p : ℝ) ^ 6 * (2 : ℝ) ^ (2 * B_boot p) *
              Real.exp (-((5 : ℝ) / 2) * ((B_boot p : ℝ) + (b_N p : ℝ)))) := by
        rw [← ENNReal.ofReal_natCast, Nat.cast_mul, Nat.cast_pow, Nat.cast_pow,
          Nat.cast_ofNat, ← ENNReal.ofReal_mul (by positivity)]
      _ ≤ ENNReal.ofReal (1 / (N p : ℝ)) :=
        ENNReal.ofReal_le_ofReal (source_exponential_budget C_b hC_b p hbranch)

end Bandits.Support.FalseForwardContextUnion

end
