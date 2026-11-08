/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.BootstrapDimensions
public import Bandits.Support.BootstrapStartupCostScale
public import Bandits.Support.ConstructorDimensions
public import Bandits.Support.GeneratedBootstrapGainBudget
public import Bandits.Support.GeneratedBootstrapPotential
public import Bandits.Support.GeneratedLatentActivityTail
public import Bandits.Support.GeneratedProductiveExitBudget
public import Bandits.Support.ProductSetLaw
public import Bandits.Support.ReferenceInitializationRun

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Deterministic uninformed support obstruction

This module proves the source's unfinished-support implication on the existing
reference initialization run. It uses only the actual finite potential and
full-stay budgets, together with the literal productive and latent-activity
obstructions. It introduces no conditional-mean or good-event premise.

Sources: `sources/zip4/manuscript/appendix_b_communication.tex:572-635` and
`sources/zip4/manuscript/07_public_setup.tex:106-140`.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.ActiveRoundActions
open scoped BigOperators

namespace Bandits.Support.GeneratedUninformedSupportObstruction

abbrev Parameters := ConstructorDimensions.Parameters

variable {p : Parameters}

/-- Rounded-reward support on the first `r` actual bootstrap blocks. Each
index is included canonically into the full bootstrap horizon. -/
def supportCountPrefix (x : ReferenceInitializationRun.Input p) (r : ℕ)
    (hr : r ≤ n_boot p) (a : Fin p.K) : ℝ :=
  ∑ s : Fin r, GeneratedBootstrapGainBudget.rewardSupportCountAt x
    ⟨s.val, s.isLt.trans_le hr⟩ a

/-- Actual importance on the same finite prefix and arm. -/
def importancePrefix (x : ReferenceInitializationRun.Input p)
    (i : Follower p.m) (r : ℕ) (hr : r ≤ n_boot p) (a : Fin p.K) : ℝ :=
  ∑ s : Fin r, GeneratedBootstrapPotential.actualImportance x i
    ⟨s.val, s.isLt.trans_le hr⟩ a

/-- Actual productive-block count on the same finite prefix. -/
def productivePrefixCount (x : ReferenceInitializationRun.Input p)
    (i : Follower p.m) (r : ℕ) (hr : r ≤ n_boot p) : ℝ :=
  ∑ s : Fin r, GeneratedBootstrapGainBudget.productiveIndicator x i
    ⟨s.val, s.isLt.trans_le hr⟩

/-- Original latent activity count on the same finite prefix. -/
def latentActivityPrefixCount (x : ReferenceInitializationRun.Input p)
    (i : Follower p.m) (r : ℕ) (hr : r ≤ n_boot p) : ℝ :=
  ∑ s : Fin r, GeneratedBootstrapGainBudget.latentActivityIndicator x i
    ⟨s.val, s.isLt.trans_le hr⟩

/-- The original latent activity indicator summed on the canonical `Fin r`
prefix is exactly the accepted extended-coordinate prefix count. -/
theorem latentActivityPrefixCount_eq_extendedActivityPrefixCount
    (x : ReferenceInitializationRun.Input p) (i : Follower p.m)
    (r : ℕ) (hr : r ≤ n_boot p) :
    latentActivityPrefixCount x i r hr =
      GeneratedLatentActivityTail.extendedActivityPrefixCount p i r x.coordinates := by
  classical
  unfold latentActivityPrefixCount
    GeneratedLatentActivityTail.extendedActivityPrefixCount
  refine Finset.sum_bij
    (fun s _ => (⟨s.val, s.isLt.trans_le hr⟩ : Fin (n_boot p))) ?_ ?_ ?_ ?_
  · intro s hs
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, s.isLt⟩
  · intro s₁ hs₁ s₂ hs₂ heq
    have hv : (⟨s₁.val, s₁.isLt.trans_le hr⟩ : Fin (n_boot p)).val =
        (⟨s₂.val, s₂.isLt.trans_le hr⟩ : Fin (n_boot p)).val :=
      congrArg (fun z : Fin (n_boot p) => z.val) heq
    exact Fin.ext (by simpa using hv)
  · intro t ht
    rcases Finset.mem_filter.mp ht with ⟨_, htr⟩
    refine ⟨⟨t.val, htr⟩, Finset.mem_univ _, ?_⟩
    exact Fin.ext rfl
  · intro s hs
    dsimp [GeneratedBootstrapGainBudget.latentActivityIndicator,
      GeneratedBootstrapGainBudget.latentBlockProfileAt,
      PrivateSourceStreams.blockDrawProfileMap,
      PrivateSourceStreams.privateBlockDrawMap]
    by_cases hcoin : PrivateSourceStreams.activityScalarDraw p
        (((x.coordinates.1.1 ⟨s.val, s.isLt.trans_le hr⟩)
          (BootstrapPhysicalInput.sourceFollowerIndex p i)).1) = true
    · simp [hcoin, GeneratedLatentActivityTail.coinToReal]
    · simp [hcoin, GeneratedLatentActivityTail.coinToReal]

/-- The importance obstruction (E_I), using the actual prelaunch status,
importance, support, and source constants on this reference input. -/
def importanceObstruction (x : ReferenceInitializationRun.Input p) : Prop :=
  ∃ i : Follower p.m, ∃ a : Fin p.K, ∃ r : ℕ,
    ∃ hr : r ≤ n_boot p,
      (∀ q : ℕ, q < r →
        GeneratedProductiveExitBudget.prelaunchUninformedIndicator x i q = 1) ∧
      supportCountPrefix x r hr a >
        1024 * (p.m : ℝ) *
          (importancePrefix x i r hr a +
            2 * (p.K : ℝ) * (B_boot p : ℝ) *
              (4 * (b_N p : ℝ)))

/-- The productive-block-count obstruction (E_P) on this input's actual
reference-run prefix. -/
def productiveObstruction (x : ReferenceInitializationRun.Input p) : Prop :=
  ∃ i : Follower p.m, ∃ r : ℕ, ∃ hr : r ≤ n_boot p,
    productivePrefixCount x i r hr >
      32 * (p.K : ℝ) * (1 + 4 * (b_N p : ℝ))

/-- The accepted extended-private-coordinate latent-activity tail event
(E_A), reused without changing its carrier or law. -/
def latentActivityObstruction (x : ReferenceInitializationRun.Input p) : Prop :=
  ∃ i : Follower p.m,
    x.coordinates ∈ GeneratedLatentActivityTail.extendedActivityTailEvent p i

/-- On every incoming-uninformed prefix with comparator support above `Q`, at
least one of the literal importance, productive-count, and latent-activity
obstructions occurs. The sole scalar premise is the stated lower bound on
`x.C_star`; the run and all observables come from `x` itself. -/
theorem unfinishedSupport_obstruction_subset
    (x : ReferenceInitializationRun.Input p)
    (hCstar : (2 : ℝ) ^ 20 ≤ x.C_star)
    (htarget : ∃ i : Follower p.m, ∃ r : ℕ,
      ∃ hr : r ≤ n_boot p, ∃ S : Finset (Fin p.K),
        S ∈ ProductSetLaw.support p.K p.m ∧
        (∀ q : ℕ, q < r →
          GeneratedProductiveExitBudget.prelaunchUninformedIndicator x i q = 1) ∧
        (BootstrapStartupCostScale.Q x.C_star x.C_h p : ℝ) <
          ∑ a ∈ S, supportCountPrefix x r hr a) :
    importanceObstruction x ∨ productiveObstruction x ∨
      latentActivityObstruction x := by
  classical
  rcases htarget with ⟨i, r, hr, S, hS, hV, hlarge⟩
  by_cases hI : importanceObstruction x
  · exact Or.inl hI
  by_cases hP : productiveObstruction x
  · exact Or.inr (Or.inl hP)
  by_cases hA : latentActivityObstruction x
  · exact Or.inr (Or.inr hA)
  let m : ℝ := p.m
  let k : ℝ := p.K
  let B : ℝ := B_boot p
  let b : ℝ := b_N p
  let h : ℝ := GeneratedBootstrapGainBudget.startupThreshold x
  let ell : ℝ := 4 * b
  let U : ℝ := 2 * k * B
  let core : ℝ := m ^ 2 * k * B * b + m * h * (n_boot p : ℝ) +
    m ^ 2 * h * b + m * B
  have hm : 0 < m := by
    dsimp [m]
    exact Nat.cast_pos.mpr (ConstructorDimensions.m_pos p)
  have hm0 : 0 ≤ m := hm.le
  have hk0 : 0 ≤ k := by dsimp [k]; positivity
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  have hb0 : 0 ≤ b := by dsimp [b]; positivity
  have hb1 : 1 ≤ b := by
    dsimp [b]
    exact_mod_cast Nat.succ_le_of_lt (ConstructorDimensions.b_N_pos p)
  have hh0 : 0 ≤ h := by dsimp [h]; positivity
  have hU0 : 0 ≤ U := by dsimp [U]; positivity
  have hell_eq : ell = 4 * b := rfl
  have hIarm (a : Fin p.K) :
      supportCountPrefix x r hr a ≤
        1024 * m * (importancePrefix x i r hr a + U * ell) := by
    by_contra hnot
    apply hI
    refine ⟨i, a, r, hr, hV, ?_⟩
    exact lt_of_not_ge hnot
  have hPcount : productivePrefixCount x i r hr ≤ 32 * k * (1 + ell) := by
    by_contra hnot
    apply hP
    exact ⟨i, r, hr, lt_of_not_ge hnot⟩
  have hnotActivity :
      x.coordinates ∉ GeneratedLatentActivityTail.extendedActivityTailEvent p i := by
    intro hmem
    exact hA ⟨i, hmem⟩
  have hnotActivity' :
      ∀ q : {q : ℕ // q ≤ n_boot p},
        ¬ (2 * (q.1 : ℝ) / (p.m : ℝ) + 4 * (b_N p : ℝ) <
          GeneratedLatentActivityTail.extendedActivityPrefixCount
            p i q.1 x.coordinates) := by
    simpa only [GeneratedLatentActivityTail.extendedActivityTailEvent,
      Set.mem_ofPred_eq, not_exists] using hnotActivity
  have hActivityCount :
      latentActivityPrefixCount x i r hr ≤
        2 * (r : ℝ) / m + ell := by
    rw [latentActivityPrefixCount_eq_extendedActivityPrefixCount]
    have hcount := hnotActivity' ⟨r, hr⟩
    have hcount' :
        GeneratedLatentActivityTail.extendedActivityPrefixCount
            p i r x.coordinates ≤
          2 * (r : ℝ) / (p.m : ℝ) + 4 * (b_N p : ℝ) :=
      not_lt.mp hcount
    simpa [m, ell, b] using hcount'
  have hkpos : 0 < k := by
    dsimp [k]
    exact Nat.cast_pos.mpr (ConstructorDimensions.K_pos p)
  have hNpos : 0 < (ConstructorDimensions.N p : ℝ) :=
    Nat.cast_pos.mpr (ConstructorDimensions.N_pos p)
  have hKN : (p.K : ℝ) ≤ (ConstructorDimensions.N p : ℝ) :=
    Nat.cast_le.mpr (ConstructorDimensions.K_le_N p)
  have hKarg : k ≤ 2 * (ConstructorDimensions.N p : ℝ) := by
    dsimp [k]
    nlinarith [hKN, hNpos.le]
  have hlogK : Real.log k ≤ 2 * b := by
    calc
      Real.log k ≤ Real.log (2 * (ConstructorDimensions.N p : ℝ)) :=
        Real.log_le_log hkpos hKarg
      _ ≤ 2 * b := by
        simpa [b] using ConstructorDimensions.log_two_mul_N_le p
  have hpot (a : Fin p.K) : importancePrefix x i r hr a ≤
      4 * (∑ s : Fin r,
        (GeneratedBootstrapGainBudget.fullStayGainAt x i
          ⟨s.val, s.isLt.trans_le hr⟩ : ℝ)) +
        8 * (p.K : ℝ) * (B_boot p : ℝ) * Real.log (p.K : ℝ) := by
    simpa only [importancePrefix,
      GeneratedBootstrapGainBudget.fullStayGainAt] using
      GeneratedBootstrapPotential.actual_run_finite_bootstrap_potential_bound
        x i r hr a
  have hgain :
      (∑ s : Fin r,
        (GeneratedBootstrapGainBudget.fullStayGainAt x i
          ⟨s.val, s.isLt.trans_le hr⟩ : ℝ)) ≤
        (B_boot p : ℝ) * productivePrefixCount x i r hr +
          (GeneratedBootstrapGainBudget.startupThreshold x : ℝ) *
            latentActivityPrefixCount x i r hr := by
    simpa only [productivePrefixCount, latentActivityPrefixCount] using
      GeneratedBootstrapGainBudget.fullStayGain_prefix_budget x i r hr
  have hImpUpper (a : Fin p.K) : importancePrefix x i r hr a ≤
      4 * (B * (32 * k * (1 + ell)) +
        h * (2 * (r : ℝ) / m + ell)) + 8 * k * B * (2 * b) := by
    have hproductiveMul :
        B * productivePrefixCount x i r hr ≤ B * (32 * k * (1 + ell)) :=
      mul_le_mul_of_nonneg_left hPcount hB0
    have hactivityMul :
        h * latentActivityPrefixCount x i r hr ≤
          h * (2 * (r : ℝ) / m + ell) :=
      mul_le_mul_of_nonneg_left hActivityCount hh0
    have hgainBound :
        B * productivePrefixCount x i r hr +
            h * latentActivityPrefixCount x i r hr ≤
          B * (32 * k * (1 + ell)) + h * (2 * (r : ℝ) / m + ell) :=
      add_le_add hproductiveMul hactivityMul
    have hlogBound :
        8 * k * B * Real.log k ≤ 8 * k * B * (2 * b) :=
      mul_le_mul_of_nonneg_left hlogK (by positivity)
    calc
      importancePrefix x i r hr a ≤
          4 * (∑ s : Fin r,
            (GeneratedBootstrapGainBudget.fullStayGainAt x i
              ⟨s.val, s.isLt.trans_le hr⟩ : ℝ)) +
            8 * (p.K : ℝ) * (B_boot p : ℝ) * Real.log (p.K : ℝ) := hpot a
      _ ≤ 4 * (B * productivePrefixCount x i r hr +
            h * latentActivityPrefixCount x i r hr) +
            8 * k * B * Real.log k := by
          have hfirst := mul_le_mul_of_nonneg_left hgain (by norm_num : (0 : ℝ) ≤ 4)
          have hsecond :
              8 * (p.K : ℝ) * (B_boot p : ℝ) * Real.log (p.K : ℝ) =
                8 * k * B * Real.log k := by rfl
          rw [hsecond]
          exact add_le_add hfirst le_rfl
      _ ≤ 4 * (B * (32 * k * (1 + ell)) +
            h * (2 * (r : ℝ) / m + ell)) +
            8 * k * B * Real.log k := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left hgainBound (by norm_num)) le_rfl
      _ ≤ 4 * (B * (32 * k * (1 + ell)) +
            h * (2 * (r : ℝ) / m + ell)) + 8 * k * B * (2 * b) :=
          add_le_add le_rfl hlogBound
  have hIexpanded (a : Fin p.K) :
      1024 * m * (importancePrefix x i r hr a + U * ell) ≤
        131072 * m * k * B * (1 + ell) + 8192 * h * r +
          16384 * m * h * b + 16384 * m * k * B * b +
          8192 * m * k * B * b := by
    have hbase :
        importancePrefix x i r hr a + U * ell ≤
          4 * (B * (32 * k * (1 + ell)) +
            h * (2 * (r : ℝ) / m + ell)) +
            8 * k * B * (2 * b) + U * ell :=
      by linarith [hImpUpper a]
    have hEq :
        1024 * m * (4 * (B * (32 * k * (1 + ell)) +
            h * (2 * (r : ℝ) / m + ell)) +
            8 * k * B * (2 * b) + U * ell) =
          131072 * m * k * B * (1 + ell) + 8192 * h * r +
            16384 * m * h * b + 16384 * m * k * B * b +
            8192 * m * k * B * b := by
      dsimp [U, ell]
      field_simp [ne_of_gt hm]
      ring
    calc
      1024 * m * (importancePrefix x i r hr a + U * ell) ≤
          1024 * m * (4 * (B * (32 * k * (1 + ell)) +
            h * (2 * (r : ℝ) / m + ell)) +
            8 * k * B * (2 * b) + U * ell) :=
        mul_le_mul_of_nonneg_left hbase (by positivity)
      _ = 131072 * m * k * B * (1 + ell) + 8192 * h * r +
            16384 * m * h * b + 16384 * m * k * B * b +
            8192 * m * k * B * b := hEq
  have h1ell : 1 + ell ≤ 5 * b := by
    dsimp [ell]
    nlinarith [hb1]
  have hPterm :
      131072 * m * k * B * (1 + ell) ≤ 655360 * m * k * B * b := by
    calc
      131072 * m * k * B * (1 + ell) ≤
          131072 * m * k * B * (5 * b) :=
        mul_le_mul_of_nonneg_left h1ell (by positivity)
      _ = 655360 * m * k * B * b := by ring
  have hArmBound (a : Fin p.K) :
      supportCountPrefix x r hr a ≤
        679936 * m * k * B * b + 8192 * h * r + 16384 * m * h * b := by
    calc
      supportCountPrefix x r hr a ≤
          1024 * m * (importancePrefix x i r hr a + U * ell) := hIarm a
      _ ≤ 131072 * m * k * B * (1 + ell) + 8192 * h * r +
            16384 * m * h * b + 16384 * m * k * B * b +
            8192 * m * k * B * b := hIexpanded a
      _ ≤ 655360 * m * k * B * b + 8192 * h * r +
            16384 * m * h * b + 16384 * m * k * B * b +
            8192 * m * k * B * b := by
        linarith [hPterm]
      _ = 679936 * m * k * B * b + 8192 * h * r + 16384 * m * h * b := by
        ring
  have hcard : S.card = p.m := by
    change S ∈ Finset.univ.powersetCard p.m at hS
    exact (Finset.mem_powersetCard.mp hS).2
  have hsumBound :
      (∑ a ∈ S, supportCountPrefix x r hr a) ≤
        679936 * m ^ 2 * k * B * b + 8192 * m * h * r +
          16384 * m ^ 2 * h * b := by
    have hsum := Finset.sum_le_sum (s := S) (fun a ha => hArmBound a)
    calc
      (∑ a ∈ S, supportCountPrefix x r hr a) ≤
          ∑ a ∈ S,
            (679936 * m * k * B * b + 8192 * h * r + 16384 * m * h * b) :=
        hsum
      _ = (S.card : ℝ) *
            (679936 * m * k * B * b + 8192 * h * r + 16384 * m * h * b) := by
        simp only [Finset.sum_const, nsmul_eq_mul]
      _ = 679936 * m ^ 2 * k * B * b + 8192 * m * h * r +
            16384 * m ^ 2 * h * b := by
        rw [hcard]
        dsimp [m]
        ring
  have hrReal : (r : ℝ) ≤ (n_boot p : ℝ) := by exact_mod_cast hr
  have hsumHorizon :
      679936 * m ^ 2 * k * B * b + 8192 * m * h * r +
          16384 * m ^ 2 * h * b ≤
        679936 * m ^ 2 * k * B * b + 8192 * m * h * (n_boot p : ℝ) +
          16384 * m ^ 2 * h * b := by
    have hmul := mul_le_mul_of_nonneg_left hrReal (by positivity : 0 ≤ 8192 * m * h)
    exact add_le_add (add_le_add le_rfl hmul) le_rfl
  have hcoef1 : (679936 : ℝ) ≤ (2 : ℝ) ^ 20 := by norm_num
  have hcoef2 : (8192 : ℝ) ≤ (2 : ℝ) ^ 20 := by norm_num
  have hcoef3 : (16384 : ℝ) ≤ (2 : ℝ) ^ 20 := by norm_num
  have hterm1 :
      679936 * m ^ 2 * k * B * b ≤ (2 : ℝ) ^ 20 * (m ^ 2 * k * B * b) := by
    calc
      679936 * m ^ 2 * k * B * b = 679936 * (m ^ 2 * k * B * b) := by ring
      _ ≤ (2 : ℝ) ^ 20 * (m ^ 2 * k * B * b) :=
        mul_le_mul_of_nonneg_right hcoef1 (by positivity)
  have hterm2 :
      8192 * m * h * (n_boot p : ℝ) ≤
        (2 : ℝ) ^ 20 * (m * h * (n_boot p : ℝ)) := by
    calc
      8192 * m * h * (n_boot p : ℝ) =
          8192 * (m * h * (n_boot p : ℝ)) := by ring
      _ ≤ (2 : ℝ) ^ 20 * (m * h * (n_boot p : ℝ)) :=
        mul_le_mul_of_nonneg_right hcoef2 (by positivity)
  have hterm3 :
      16384 * m ^ 2 * h * b ≤ (2 : ℝ) ^ 20 * (m ^ 2 * h * b) := by
    calc
      16384 * m ^ 2 * h * b = 16384 * (m ^ 2 * h * b) := by ring
      _ ≤ (2 : ℝ) ^ 20 * (m ^ 2 * h * b) :=
        mul_le_mul_of_nonneg_right hcoef3 (by positivity)
  have hsubcore :
      m ^ 2 * k * B * b + m * h * (n_boot p : ℝ) + m ^ 2 * h * b ≤ core := by
    dsimp [core]
    exact le_add_of_nonneg_right (mul_nonneg hm0 hB0)
  have hscaleTerm :
      679936 * m ^ 2 * k * B * b + 8192 * m * h * (n_boot p : ℝ) +
          16384 * m ^ 2 * h * b ≤ (2 : ℝ) ^ 20 * core := by
    calc
      _ ≤ (2 : ℝ) ^ 20 * (m ^ 2 * k * B * b) +
            (2 : ℝ) ^ 20 * (m * h * (n_boot p : ℝ)) +
            (2 : ℝ) ^ 20 * (m ^ 2 * h * b) := by
        exact add_le_add (add_le_add hterm1 hterm2) hterm3
      _ = (2 : ℝ) ^ 20 *
            (m ^ 2 * k * B * b + m * h * (n_boot p : ℝ) + m ^ 2 * h * b) := by
        ring
      _ ≤ (2 : ℝ) ^ 20 * core :=
        mul_le_mul_of_nonneg_left hsubcore (by positivity)
  have hcore0 : 0 ≤ core := by
    dsimp [core, m, k, B, b, h]
    positivity
  have hCscale : (2 : ℝ) ^ 20 * core ≤ x.C_star * core :=
    mul_le_mul_of_nonneg_right hCstar hcore0
  have hceil : x.C_star * core ≤
      (BootstrapStartupCostScale.Q x.C_star x.C_h p : ℝ) := by
    unfold BootstrapStartupCostScale.Q
    change x.C_star *
        ((p.m : ℝ) ^ 2 * (p.K : ℝ) * (B_boot p : ℝ) * (b_N p : ℝ) +
          (p.m : ℝ) *
            (BootstrapStartupCostScale.h_boot x.C_h p : ℝ) *
            (n_boot p : ℝ) +
          (p.m : ℝ) ^ 2 *
            (BootstrapStartupCostScale.h_boot x.C_h p : ℝ) *
            (b_N p : ℝ) + (p.m : ℝ) * (B_boot p : ℝ)) ≤
      (⌈x.C_star *
        ((p.m : ℝ) ^ 2 * (p.K : ℝ) * (B_boot p : ℝ) * (b_N p : ℝ) +
          (p.m : ℝ) *
            (BootstrapStartupCostScale.h_boot x.C_h p : ℝ) *
            (n_boot p : ℝ) +
          (p.m : ℝ) ^ 2 *
            (BootstrapStartupCostScale.h_boot x.C_h p : ℝ) *
            (b_N p : ℝ) + (p.m : ℝ) * (B_boot p : ℝ))⌉₊ : ℝ)
    exact Nat.le_ceil _
  have hsumLeQ :
      (∑ a ∈ S, supportCountPrefix x r hr a) ≤
        (BootstrapStartupCostScale.Q x.C_star x.C_h p : ℝ) := by
    calc
      (∑ a ∈ S, supportCountPrefix x r hr a) ≤
          679936 * m ^ 2 * k * B * b + 8192 * m * h * r +
            16384 * m ^ 2 * h * b := hsumBound
      _ ≤ 679936 * m ^ 2 * k * B * b +
            8192 * m * h * (n_boot p : ℝ) + 16384 * m ^ 2 * h * b :=
        hsumHorizon
      _ ≤ (2 : ℝ) ^ 20 * core := hscaleTerm
      _ ≤ x.C_star * core := hCscale
      _ ≤ (BootstrapStartupCostScale.Q x.C_star x.C_h p : ℝ) := hceil
  exact False.elim ((not_lt_of_ge hsumLeQ) hlarge)

end Bandits.Support.GeneratedUninformedSupportObstruction

end
