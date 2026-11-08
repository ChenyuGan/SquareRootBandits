/-
Copyright (c) 2026 Bandits Lean regret formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.TuningSourceDimensions
public import Bandits.Support.DyadicRateSelection
public import Bandits.Support.RateTuningAlgebra
public import Bandits.Support.ConstructorDimensions
public import Bandits.Support.CanonicalRecordingRates
public import Bandits.Support.PublicGridConcentration

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The source dyadic learning rate

The literal rate of `sources/zip4/manuscript/08_main_theorem.tex:4-24` is the
accepted largest-dyadic selector at the minimum of the stability cap and the
square-root cutoff. The stability cap is from
`sources/zip4/manuscript/04_slow_fast_learner.tex:96-103`. The numerical objective
and denominator penalty are used at
`sources/zip4/manuscript/08_main_theorem.tex:142-155`.

One positive real `C1` is fixed before all constructor parameters. A single
branch constant and a single natural threshold then work uniformly in those
parameters. The threshold is proved using logarithmic sublinear growth, rather
than supplied as a premise. No claim here identifies a sufficient `C1` for the
transport or learning estimates, assembles physical regret, or closes a
manuscript theorem.
-/

public section

namespace Bandits.Support.SourceDyadicTuning

open Bandits.Support.ConstructorDimensions
open Bandits.Support.TuningSourceDimensions
open Bandits.Support.DyadicRateSelection

/-- The literal upper bound on the source learning rate. -/
@[expose] noncomputable def stabilityCap (p : Parameters) : ℝ :=
  1 / (1024 * (p.m : ℝ) * (p.K : ℝ) * (CanonicalRecordingRates.L_stab p : ℝ))

/-- The source square-root cutoff, using the integrated definitions `J` and `W`. -/
@[expose] noncomputable def tuningRoot (C1 : ℝ) (p : Parameters) : ℝ :=
  Real.sqrt ((J p : ℝ) / (W C1 p * (p.T : ℝ)))

theorem stabilityCap_pos (p : Parameters) : 0 < stabilityCap p := by
  have hm : 0 < (p.m : ℝ) := Nat.cast_pos.mpr (ConstructorDimensions.m_pos p)
  have hK : 0 < (p.K : ℝ) := Nat.cast_pos.mpr (ConstructorDimensions.K_pos p)
  have hL : 0 < (CanonicalRecordingRates.L_stab p : ℝ) := by
    exact_mod_cast (Nat.zero_lt_one.trans_le (CanonicalRecordingRates.L_stab_ge_one p))
  unfold stabilityCap
  positivity

theorem tuningRoot_pos (C1 : ℝ) (hC1 : 0 < C1) (p : Parameters) :
    0 < tuningRoot C1 p := by
  exact Real.sqrt_pos.2 (div_pos (Nat.cast_pos.mpr (J_pos p))
    (mul_pos (W_pos C1 p hC1) (Nat.cast_pos.mpr (ConstructorDimensions.T_pos p))))

/-- A positive cutoff on the entire source parameter domain; there is no default
rate or fallback branch. -/
@[expose] noncomputable def sourceCutoff (C1 : ℝ) (hC1 : 0 < C1)
    (p : Parameters) : PositiveCutoff :=
  ⟨min (stabilityCap p) (tuningRoot C1 p),
    lt_min (stabilityCap_pos p) (tuningRoot_pos C1 hC1 p)⟩

/-- The actual source rate is the largest dyadic below the literal positive
minimum cutoff. Its sole numerical input beyond the source parameters is the
universal positive coefficient `C1`. -/
@[expose] noncomputable def sourceRate (C1 : ℝ) (hC1 : 0 < C1)
    (p : Parameters) : ℝ :=
  dyadicRate (sourceCutoff C1 hC1 p)

/-- For nonnegative rates, the original quadratic constraint and the square-root
constraint are equivalent. -/
theorem le_tuningRoot_iff (C1 : ℝ) (hC1 : 0 < C1) (p : Parameters)
    {eta : ℝ} (heta : 0 ≤ eta) :
    eta ≤ tuningRoot C1 p ↔ eta ^ 2 * W C1 p * (p.T : ℝ) ≤ (J p : ℝ) := by
  have hT : 0 < (p.T : ℝ) := Nat.cast_pos.mpr (ConstructorDimensions.T_pos p)
  have hWT := mul_pos (W_pos C1 p hC1) hT
  rw [tuningRoot, Real.le_sqrt heta
    (div_nonneg (Nat.cast_nonneg _) hWT.le), le_div_iff₀ hWT]
  rw [mul_assoc]

/-- The exponent is an integer, with an explicit formula. -/
theorem sourceRate_eq_intPower (C1 : ℝ) (hC1 : 0 < C1) (p : Parameters) :
    sourceRate C1 hC1 p = (2 : ℝ) ^
      (-Int.ceil (Real.logb 2 (1 / (sourceCutoff C1 hC1 p).1))) :=
  dyadicRate_eq_intPower _

theorem sourceRate_bounds (C1 : ℝ) (hC1 : 0 < C1) (p : Parameters) :
    (sourceCutoff C1 hC1 p).1 / 2 < sourceRate C1 hC1 p ∧
      sourceRate C1 hC1 p ≤ (sourceCutoff C1 hC1 p).1 :=
  dyadicRate_bounds _

theorem sourceRate_pos (C1 : ℝ) (hC1 : 0 < C1) (p : Parameters) :
    0 < sourceRate C1 hC1 p :=
  (div_pos (sourceCutoff C1 hC1 p).2 (by norm_num)).trans
    (sourceRate_bounds C1 hC1 p).1

/-- The selected rate satisfies both original constraints. -/
theorem sourceRate_admissible (C1 : ℝ) (hC1 : 0 < C1) (p : Parameters) :
    sourceRate C1 hC1 p ≤ stabilityCap p ∧
      sourceRate C1 hC1 p ^ 2 * W C1 p * (p.T : ℝ) ≤ (J p : ℝ) := by
  have hu := (sourceRate_bounds C1 hC1 p).2
  constructor
  · exact hu.trans (min_le_left _ _)
  · exact (le_tuningRoot_iff C1 hC1 p (sourceRate_pos C1 hC1 p).le).1
      (hu.trans (min_le_right _ _))

/-- Every integer power of two satisfying both original constraints is no larger
than the selected rate. -/
theorem sourceRate_maximal (C1 : ℝ) (hC1 : 0 < C1) (p : Parameters) (z : ℤ)
    (hcap : (2 : ℝ) ^ z ≤ stabilityCap p)
    (hquad : ((2 : ℝ) ^ z) ^ 2 * W C1 p * (p.T : ℝ) ≤ (J p : ℝ)) :
    (2 : ℝ) ^ z ≤ sourceRate C1 hC1 p := by
  apply dyadicRate_maximal
  exact le_min hcap ((le_tuningRoot_iff C1 hC1 p
    (zpow_pos (by norm_num : (0 : ℝ) < 2) z).le).2 hquad)

/-- Joint characterization of the largest dyadic satisfying the two original
source constraints, including membership of the selected rate. -/
theorem sourceRate_isGreatest (C1 : ℝ) (hC1 : 0 < C1) (p : Parameters) :
    IsGreatest {eta : ℝ | (∃ z : ℤ, eta = (2 : ℝ) ^ z) ∧
      eta ≤ stabilityCap p ∧ eta ^ 2 * W C1 p * (p.T : ℝ) ≤ (J p : ℝ)}
      (sourceRate C1 hC1 p) := by
  refine ⟨⟨⟨_, sourceRate_eq_intPower C1 hC1 p⟩,
    sourceRate_admissible C1 hC1 p⟩, ?_⟩
  rintro eta ⟨⟨z, rfl⟩, hcap, hquad⟩
  exact sourceRate_maximal C1 hC1 p z hcap hquad

/-- An explicit branch constant, chosen once for the already fixed `C1`. -/
@[expose] noncomputable def branchConstant (C1 : ℝ) : ℝ := max 16 (27 * 1024 ^ 2 / C1)

theorem branchConstant_pos (C1 : ℝ) : 0 < branchConstant C1 :=
  (by norm_num : (0 : ℝ) < 16).trans_le (le_max_left _ _)

/-- The integrated feasibility budget makes the square-root cutoff admissible
on every construction branch with a sufficiently large universal `Cb`. -/
theorem tuningRoot_le_stabilityCap_of_branch (C1 : ℝ) (hC1 : 0 < C1)
    (Cb : ℝ) (hCb : 27 * 1024 ^ 2 / C1 ≤ Cb) (p : Parameters)
    (hbranch : Cb * (p.m : ℝ) * (p.K : ℝ) * (b_N p : ℝ) ^ 2 < (p.T : ℝ)) :
    tuningRoot C1 p ≤ stabilityCap p := by
  let a : ℝ := 1024 * (p.m : ℝ) * (p.K : ℝ) *
    (CanonicalRecordingRates.L_stab p : ℝ)
  have ha : 0 < a := by
    have hm : 0 < (p.m : ℝ) := Nat.cast_pos.mpr (ConstructorDimensions.m_pos p)
    have hK : 0 < (p.K : ℝ) := Nat.cast_pos.mpr (ConstructorDimensions.K_pos p)
    have hL : 0 < (CanonicalRecordingRates.L_stab p : ℝ) := by
      exact_mod_cast (Nat.zero_lt_one.trans_le (CanonicalRecordingRates.L_stab_ge_one p))
    dsimp [a]
    positivity
  have hbudget : a ^ 2 * (J p : ℝ) / W C1 p < (p.T : ℝ) := by
    calc
      _ ≤ (27 * 1024 ^ 2 / C1) * (p.m : ℝ) * (p.K : ℝ) * (b_N p : ℝ) ^ 2 :=
        branch_feasibility_budget C1 p hC1
      _ ≤ Cb * (p.m : ℝ) * (p.K : ℝ) * (b_N p : ℝ) ^ 2 := by
        have hm : 0 ≤ (p.m : ℝ) := Nat.cast_nonneg _
        have hK : 0 ≤ (p.K : ℝ) := Nat.cast_nonneg _
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCb hm) hK)
          (sq_nonneg _)
      _ < (p.T : ℝ) := hbranch
  have hprod : (J p : ℝ) * a ^ 2 ≤ W C1 p * (p.T : ℝ) := by
    have h := ((div_lt_iff₀ (W_pos C1 p hC1)).1 hbudget).le
    nlinarith only [h]
  have hJ : (J p : ℝ) ≤ (W C1 p * (p.T : ℝ)) / a ^ 2 :=
    (le_div_iff₀ (pow_pos ha 2)).2 hprod
  apply (Real.sqrt_le_left (stabilityCap_pos p).le).2
  apply (div_le_iff₀ (mul_pos (W_pos C1 p hC1)
    (Nat.cast_pos.mpr (ConstructorDimensions.T_pos p)))).2
  calc
    (J p : ℝ) ≤ (W C1 p * (p.T : ℝ)) / a ^ 2 := hJ
    _ = stabilityCap p ^ 2 * (W C1 p * (p.T : ℝ)) := by
      change _ = (1 / a) ^ 2 * _
      rw [div_pow]
      ring

theorem sourceCutoff_eq_tuningRoot_of_branch (C1 : ℝ) (hC1 : 0 < C1)
    (Cb : ℝ) (hCb : 27 * 1024 ^ 2 / C1 ≤ Cb) (p : Parameters)
    (hbranch : Cb * (p.m : ℝ) * (p.K : ℝ) * (b_N p : ℝ) ^ 2 < (p.T : ℝ)) :
    (sourceCutoff C1 hC1 p).1 = tuningRoot C1 p :=
  min_eq_right (tuningRoot_le_stabilityCap_of_branch C1 hC1 Cb hCb p hbranch)

theorem sourceRate_branch_bounds (C1 : ℝ) (hC1 : 0 < C1)
    (Cb : ℝ) (hCb : 27 * 1024 ^ 2 / C1 ≤ Cb) (p : Parameters)
    (hbranch : Cb * (p.m : ℝ) * (p.K : ℝ) * (b_N p : ℝ) ^ 2 < (p.T : ℝ)) :
    tuningRoot C1 p / 2 < sourceRate C1 hC1 p ∧
      sourceRate C1 hC1 p ≤ tuningRoot C1 p := by
  rw [← sourceCutoff_eq_tuningRoot_of_branch C1 hC1 Cb hCb p hbranch]
  exact sourceRate_bounds C1 hC1 p

/-- A uniform threshold for the actual source bit length. Only the already fixed
positive `C1` determines the threshold; no constructor parameter is chosen first.
The proof combines `log x = o(x)` and the integrated ceiling-log identity. -/
theorem exists_uniform_bitLength_bound (C1 : ℝ) (hC1 : 0 < C1) :
    ∃ N0 : ℕ, ∀ p : Parameters, N0 ≤ N p →
      C1 * (b_N p : ℝ) ≤ (N p : ℝ) / 2 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc : 0 < Real.log 2 / (4 * C1) := div_pos hlog2 (by positivity)
  obtain ⟨R, hR⟩ := Filter.eventually_atTop.1 (Real.isLittleO_log_id_atTop.bound hc)
  refine ⟨max ⌈R⌉₊ ⌈4 * C1 + 1⌉₊, ?_⟩
  intro p hN
  have hnR : R ≤ (N p : ℝ) := (Nat.le_ceil R).trans (by
    exact_mod_cast ((le_max_left ⌈R⌉₊ ⌈4 * C1 + 1⌉₊).trans hN))
  have hnlarge : 4 * C1 + 1 ≤ (N p : ℝ) := (Nat.le_ceil _).trans (by
    exact_mod_cast ((le_max_right ⌈R⌉₊ ⌈4 * C1 + 1⌉₊).trans hN))
  have hx : 0 < (N p : ℝ) + 1 := by positivity
  have hnorm := hR ((N p : ℝ) + 1) (hnR.trans (by linarith))
  have hlog : Real.log ((N p : ℝ) + 1) ≤
      (Real.log 2 / (4 * C1)) * ((N p : ℝ) + 1) := by
    apply (le_abs_self _).trans
    simpa only [id_eq, Real.norm_eq_abs, abs_of_nonneg hx.le] using hnorm
  have hlogb : Real.logb 2 ((N p + 1 : ℕ) : ℝ) ≤
      ((N p : ℝ) + 1) / (4 * C1) := by
    calc
      _ = Real.log ((N p : ℝ) + 1) / Real.log 2 := by
        rw [Real.logb, Nat.cast_add, Nat.cast_one]
      _ ≤ ((Real.log 2 / (4 * C1)) * ((N p : ℝ) + 1)) / Real.log 2 :=
        div_le_div_of_nonneg_right hlog hlog2.le
      _ = ((N p : ℝ) + 1) / (4 * C1) := by
        field_simp [hC1.ne', hlog2.ne']
  have hceil : (b_N p : ℝ) < Real.logb 2 ((N p + 1 : ℕ) : ℝ) + 1 := by
    rw [b_N_eq_real_ceiling_log]
    apply Nat.ceil_lt_add_one
    exact Real.logb_nonneg (by norm_num) (by
      have hn : (0 : ℝ) ≤ (N p : ℝ) := Nat.cast_nonneg _
      push_cast
      linarith only [hn])
  calc
    C1 * (b_N p : ℝ) ≤ C1 * (Real.logb 2 ((N p + 1 : ℕ) : ℝ) + 1) :=
      mul_le_mul_of_nonneg_left hceil.le hC1.le
    _ ≤ C1 * (((N p : ℝ) + 1) / (4 * C1) + 1) :=
      mul_le_mul_of_nonneg_left (add_le_add hlogb le_rfl) hC1.le
    _ = ((N p : ℝ) + 1) / 4 + C1 := by field_simp [hC1.ne']
    _ ≤ (N p : ℝ) / 2 := by linarith only [hnlarge]

/-- The corresponding uniform ratio estimate, derived rather than assumed. -/
theorem exists_uniform_bitLength_ratio_bound (C1 : ℝ) (hC1 : 0 < C1) :
    ∃ N0 : ℕ, ∀ p : Parameters, N0 ≤ N p →
      C1 * (b_N p : ℝ) / (N p : ℝ) ≤ 1 / 2 := by
  obtain ⟨N0, hN0⟩ := exists_uniform_bitLength_bound C1 hC1
  refine ⟨N0, fun p hp => ?_⟩
  apply (div_le_iff₀ (Nat.cast_pos.mpr (ConstructorDimensions.N_pos p))).2
  simpa only [div_eq_mul_inv, one_mul, mul_comm] using hN0 p hp

/-- Internal scalar step: the proved bit-length bound, `J ≥ m`, and the literal
identity `N = 2 K m (T + 1)` imply the root lower bound. -/
theorem two_div_N_le_tuningRoot_of_bitLength_bound (C1 : ℝ) (hC1 : 0 < C1)
    (p : Parameters) (hsmall : C1 * (b_N p : ℝ) ≤ (N p : ℝ) / 2) :
    2 / (N p : ℝ) ≤ tuningRoot C1 p := by
  have hm : 0 < (p.m : ℝ) := Nat.cast_pos.mpr (ConstructorDimensions.m_pos p)
  have hK : 0 < (p.K : ℝ) := Nat.cast_pos.mpr (ConstructorDimensions.K_pos p)
  have hN : 0 < (N p : ℝ) := Nat.cast_pos.mpr (ConstructorDimensions.N_pos p)
  have hhalf : 0 ≤ (N p : ℝ) / 2 := by positivity
  have hCN : 0 ≤ C1 * (b_N p : ℝ) := mul_nonneg hC1.le (Nat.cast_nonneg _)
  have hJm : (p.m : ℝ) ≤ (J p : ℝ) := by exact_mod_cast m_le_J p
  have hN_eq : (N p : ℝ) = 2 * (p.K : ℝ) * (p.m : ℝ) * ((p.T : ℝ) + 1) := by
    simp only [N, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one]
  have hmkT : (p.m : ℝ) * (p.K : ℝ) * (p.T : ℝ) ≤ (N p : ℝ) / 2 := by
    calc
      _ ≤ (p.m : ℝ) * (p.K : ℝ) * ((p.T : ℝ) + 1) :=
        mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hm.le hK.le)
      _ = (N p : ℝ) / 2 := by rw [hN_eq]; ring
  have hWT : W C1 p * (p.T : ℝ) ≤ (J p : ℝ) * (N p : ℝ) ^ 2 / 4 := by
    calc
      _ = (p.m : ℝ) * (C1 * (b_N p : ℝ)) *
          ((p.m : ℝ) * (p.K : ℝ) * (p.T : ℝ)) := by rw [W]; ring
      _ ≤ (p.m : ℝ) * (C1 * (b_N p : ℝ)) * ((N p : ℝ) / 2) :=
        mul_le_mul_of_nonneg_left hmkT (mul_nonneg hm.le hCN)
      _ ≤ (p.m : ℝ) * ((N p : ℝ) / 2) * ((N p : ℝ) / 2) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsmall hm.le) hhalf
      _ ≤ (J p : ℝ) * ((N p : ℝ) / 2) * ((N p : ℝ) / 2) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hJm hhalf) hhalf
      _ = (J p : ℝ) * (N p : ℝ) ^ 2 / 4 := by ring
  apply (le_tuningRoot_iff C1 hC1 p (div_nonneg (by norm_num) hN.le)).2
  calc
    (2 / (N p : ℝ)) ^ 2 * W C1 p * (p.T : ℝ) =
        (4 * (W C1 p * (p.T : ℝ))) / (N p : ℝ) ^ 2 := by ring
    _ ≤ (J p : ℝ) := (div_le_iff₀ (pow_pos hN 2)).2 (by linarith only [hWT])

/-- On the branch, the same selected rate gives both source objective bounds. -/
theorem sourceRate_objective_bounds (C1 : ℝ) (hC1 : 0 < C1)
    (Cb : ℝ) (hCb : 27 * 1024 ^ 2 / C1 ≤ Cb) (p : Parameters)
    (hbranch : Cb * (p.m : ℝ) * (p.K : ℝ) * (b_N p : ℝ) ^ 2 < (p.T : ℝ)) :
    (J p : ℝ) / sourceRate C1 hC1 p + W C1 p * sourceRate C1 hC1 p * (p.T : ℝ) ≤
        3 * Real.sqrt ((J p : ℝ) * W C1 p * (p.T : ℝ)) ∧
      (J p : ℝ) / sourceRate C1 hC1 p + W C1 p * sourceRate C1 hC1 p * (p.T : ℝ) ≤
        3 * Real.sqrt (3 * C1) * PublicGridConcentration.rowConcentrationScale p := by
  have hb := sourceRate_branch_bounds C1 hC1 Cb hCb p hbranch
  have hobj := RateTuningAlgebra.rate_objective_bound
    (Nat.cast_pos.mpr (J_pos p)) (W_pos C1 p hC1)
    (Nat.cast_pos.mpr (ConstructorDimensions.T_pos p)) (sourceRate_pos C1 hC1 p)
    (by simpa only [tuningRoot, div_eq_mul_inv, one_div, one_mul, mul_comm] using hb.1) hb.2
  refine ⟨hobj, hobj.trans ?_⟩
  calc
    _ ≤ 3 * (Real.sqrt (3 * C1) * PublicGridConcentration.rowConcentrationScale p) :=
      mul_le_mul_of_nonneg_left (sqrt_J_mul_W_mul_T_le_scale C1 p hC1) (by norm_num)
    _ = _ := by ring

/-- The source denominator penalty uses this very same rate, without a separate
choice or an additional large-size hypothesis. -/
theorem sourceRate_penalty_comparison (C1 : ℝ) (hC1 : 0 < C1) (p : Parameters) :
    (p.m : ℝ) * (p.T : ℝ) / (sourceRate C1 hC1 p * (D p : ℝ)) ≤
      (J p : ℝ) / sourceRate C1 hC1 p :=
  RateTuningAlgebra.parameter_penalty_comparison p
    (by exact_mod_cast m_le_J p) (sourceRate_pos C1 hC1 p)

/-- Joint uniform tuning: `Cb` and `N0` follow the single fixed positive `C1`
and precede every `p`. All conclusions concern the one literal selected rate.
This is numerical source tuning, not a physical regret or manuscript closure. -/
theorem sourceRate_uniform_tuning (C1 : ℝ) (hC1 : 0 < C1) :
    ∃ Cb : ℝ, ∃ N0 : ℕ, 0 < Cb ∧ max 16 (27 * 1024 ^ 2 / C1) ≤ Cb ∧
      ∀ p : Parameters,
        Cb * (p.m : ℝ) * (p.K : ℝ) * (b_N p : ℝ) ^ 2 < (p.T : ℝ) → N0 ≤ N p →
        (sourceCutoff C1 hC1 p).1 = tuningRoot C1 p ∧
        tuningRoot C1 p / 2 < sourceRate C1 hC1 p ∧
        sourceRate C1 hC1 p ≤ tuningRoot C1 p ∧
        1 / (N p : ℝ) ≤ sourceRate C1 hC1 p ∧
        (∃ n : ℕ, 0 < n ∧ (n : ℝ) = sourceRate C1 hC1 p * (D p : ℝ)) ∧
        ((J p : ℝ) / sourceRate C1 hC1 p + W C1 p * sourceRate C1 hC1 p * (p.T : ℝ) ≤
          3 * Real.sqrt ((J p : ℝ) * W C1 p * (p.T : ℝ))) ∧
        ((J p : ℝ) / sourceRate C1 hC1 p + W C1 p * sourceRate C1 hC1 p * (p.T : ℝ) ≤
          3 * Real.sqrt (3 * C1) * PublicGridConcentration.rowConcentrationScale p) ∧
        (p.m : ℝ) * (p.T : ℝ) / (sourceRate C1 hC1 p * (D p : ℝ)) ≤
          (J p : ℝ) / sourceRate C1 hC1 p := by
  obtain ⟨N0, hN0⟩ := exists_uniform_bitLength_bound C1 hC1
  refine ⟨branchConstant C1, N0, branchConstant_pos C1, le_rfl, ?_⟩
  intro p hbranch hN
  have hCb : 27 * 1024 ^ 2 / C1 ≤ branchConstant C1 := le_max_right _ _
  have hcut := sourceCutoff_eq_tuningRoot_of_branch C1 hC1 _ hCb p hbranch
  have hb := sourceRate_branch_bounds C1 hC1 _ hCb p hbranch
  have hroot := two_div_N_le_tuningRoot_of_bitLength_bound C1 hC1 p (hN0 p hN)
  have hetaN : 1 / (N p : ℝ) ≤ sourceRate C1 hC1 p := by
    have hhalf : 1 / (N p : ℝ) ≤ tuningRoot C1 p / 2 := by
      calc
        1 / (N p : ℝ) = (2 / (N p : ℝ)) / 2 := by ring
        _ ≤ tuningRoot C1 p / 2 := div_le_div_of_nonneg_right hroot (by norm_num)
    exact hhalf.trans hb.1.le
  have hDcut : 1 / (D p : ℝ) ≤ (sourceCutoff C1 hC1 p).1 := by
    calc
      _ ≤ 1 / (N p : ℝ) := one_div_le_one_div_of_le
        (Nat.cast_pos.mpr (ConstructorDimensions.N_pos p))
        (by exact_mod_cast (ConstructorDimensions.N_lt_D p).le)
      _ ≤ sourceRate C1 hC1 p := hetaN
      _ ≤ (sourceCutoff C1 hC1 p).1 := (sourceRate_bounds C1 hC1 p).2
  obtain ⟨n, hn⟩ := dyadicRate_mul_pow_two_isNat (sourceCutoff C1 hC1 p) (b_N p) hDcut
  have hn_eq : (n : ℝ) = sourceRate C1 hC1 p * (D p : ℝ) := hn.symm
  have hn_pos : 0 < n := by
    have hpos : (0 : ℝ) < (n : ℝ) := by
      rw [hn_eq]
      exact mul_pos (sourceRate_pos C1 hC1 p)
        (Nat.cast_pos.mpr (ConstructorDimensions.D_pos p))
    exact_mod_cast hpos
  have hobj := sourceRate_objective_bounds C1 hC1 _ hCb p hbranch
  exact ⟨hcut, hb.1, hb.2, hetaN, ⟨n, hn_pos, hn_eq⟩,
    hobj.1, hobj.2, sourceRate_penalty_comparison C1 hC1 p⟩

end Bandits.Support.SourceDyadicTuning

end
