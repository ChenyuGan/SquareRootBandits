/-
Copyright (c) 2026 Bandits Lean regret formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.IdentificationLocalRowBalance
public import Bandits.Support.RareTailBound
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Global identification-array block balance

This module assembles the already-proved per-row local-balance events into the
literal property (iii) over every bootstrap block and every binary support on
that block. It uses the source construction branch only for the horizon
estimate. Sources: `sources/zip4/manuscript/appendix_b_communication.tex:193-244`
and `sources/zip4/manuscript/07_public_setup.tex:5-25`.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Bandits.Support.IdentificationBlockBalance

open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.CompletePublicTable
open Bandits.Support.IdentificationLocalRowBalance

/-- The number of ID labels whose row satisfies the existing local-balance
predicate on the given actual block and support. -/
@[expose] noncomputable def propertyIIIGoodRowCount (p : Parameters)
    (id : IDArray p) (s : Fin (n_boot p)) (x : BlockSupport p s) : ℕ :=
  by
    classical
    exact (Finset.univ.filter fun u : Fin (A_id p) =>
      id ∈ localBalanceRowEvent p s x u).card

/-- The literal simultaneous source property (iii), including empty supports
and the clipped final calendar block. Source: `appendix_b_communication.tex:193-203,231-244`.
-/
@[expose] noncomputable def propertyIII (p : Parameters) (id : IDArray p) : Prop :=
  ∀ s : Fin (n_boot p), ∀ x : BlockSupport p s,
    (3 * (A_id p : ℝ)) / 4 ≤
      (propertyIIIGoodRowCount p id s x : ℝ)

/-- Failure of property (iii) for one actual block and one deterministic
support. -/
@[expose] noncomputable def propertyIIIFixedSupportFailureEvent (p : Parameters)
    (s : Fin (n_boot p)) (x : BlockSupport p s) : Set (IDArray p) :=
  {id | (propertyIIIGoodRowCount p id s x : ℝ) <
    (3 * (A_id p : ℝ)) / 4}

/-- The actual all-block, all-support failure event for property (iii). -/
@[expose] noncomputable def propertyIIIFailureEvent (p : Parameters) : Set (IDArray p) :=
  {id | ¬ propertyIII p id}

/-- The explicit one-row union-bound threshold `p₀` from the source proof. -/
@[expose] noncomputable def rowFailureThreshold (p : Parameters) : ℝ :=
  2 * (B_boot p : ℝ) ^ 2 * (2 : ℝ) ^ (-8 * (b_N p : ℝ))

/-- The source horizon is bounded by its literal size parameter. -/
theorem horizon_le_source_size (p : Parameters) : p.T ≤ N p := by
  have hKm : 1 ≤ p.K * p.m := by
    exact Nat.succ_le_of_lt (Nat.mul_pos (K_pos p) (m_pos p))
  have hcoef : 2 ≤ 2 * p.K * p.m := by
    calc
      2 = 2 * 1 := by norm_num
      _ ≤ 2 * (p.K * p.m) := Nat.mul_le_mul_left 2 hKm
      _ = 2 * p.K * p.m := by ring
  have hNfactor : 2 * (p.T + 1) ≤ N p := by
    change 2 * (p.T + 1) ≤ 2 * p.K * p.m * (p.T + 1)
    exact Nat.mul_le_mul_right (p.T + 1) hcoef
  have hTle : p.T ≤ 2 * (p.T + 1) := by omega
  exact hTle.trans hNfactor

/-- All dimension estimates used by the block union bound follow from the
literal constructor and bootstrap dimensions. -/
theorem propertyIII_dimension_estimates (p : Parameters) :
    n_boot p ≤ N p ∧ B_boot p ≤ N p ∧ 5 ≤ b_N p ∧
      Real.log (N p : ℝ) ≤ (b_N p : ℝ) * Real.log 2 := by
  have hTleN : p.T ≤ N p := horizon_le_source_size p
  have hblocks : n_boot p ≤ N p := (n_boot_le_T p).trans hTleN
  have hB : B_boot p ≤ N p := (B_boot_le_T p).trans hTleN
  have hN24 : 24 ≤ N p := BootstrapDimensions.twentyFour_le_N p
  have hpow : 2 ^ 4 < N p + 1 := by omega
  have hclog : 4 < Nat.clog 2 (N p + 1) :=
    (Nat.lt_clog_iff_pow_lt (by decide : 1 < 2)).2 hpow
  have hb5 : 5 ≤ b_N p := by
    change 5 ≤ Nat.clog 2 (N p + 1)
    omega
  have hNpow : N p ≤ 2 ^ b_N p := by
    have hNlt : N p < D p := N_lt_D p
    simpa [D] using hNlt.le
  have hNpos : 0 < (N p : ℝ) := Nat.cast_pos.mpr (N_pos p)
  have hND : (N p : ℝ) < (D p : ℝ) := by exact_mod_cast N_lt_D p
  have hlogD : Real.log (D p : ℝ) = (b_N p : ℝ) * Real.log 2 := by
    simp only [D, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
  have hlog2le : Real.log 2 ≤ 1 := by
    calc
      Real.log 2 ≤ 2 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
      _ = 1 := by norm_num
  have hlogN : Real.log (N p : ℝ) ≤ (b_N p : ℝ) * Real.log 2 := by
    calc
      Real.log (N p : ℝ) ≤ Real.log (D p : ℝ) :=
        (Real.log_lt_log hNpos hND).le
      _ = (b_N p : ℝ) * Real.log 2 := hlogD
  exact ⟨hblocks, hB, hb5, hlogN⟩

/-- The source's one-row threshold is positive, at most `2^(-5 b_N)`, and
has the logarithmic separation needed by the one-quarter Chernoff bound. -/
theorem rowFailureThreshold_bounds (p : Parameters) :
    0 < rowFailureThreshold p ∧
      rowFailureThreshold p ≤ (2 : ℝ) ^ (-5 * (b_N p : ℝ)) ∧
      (2 : ℝ) ^ (-5 * (b_N p : ℝ)) < (1 / 4 : ℝ) ∧
      2 * (b_N p : ℝ) ≤
        Real.log (1 / (4 * Real.exp 1 * rowFailureThreshold p)) := by
  have hdim := propertyIII_dimension_estimates p
  have hb5 : 5 ≤ (b_N p : ℝ) := by exact_mod_cast hdim.2.2.1
  have hb1 : 1 ≤ (b_N p : ℝ) := by linarith
  have hBnat : B_boot p ≤ 2 ^ b_N p :=
    hdim.2.1.trans (N_lt_D p).le
  have hBcast : (B_boot p : ℝ) ≤ ((2 ^ b_N p : ℕ) : ℝ) := by
    exact_mod_cast hBnat
  have hBpow : (B_boot p : ℝ) ≤ (2 : ℝ) ^ (b_N p : ℝ) := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat, Real.rpow_natCast] using hBcast
  have hp0 : 0 < rowFailureThreshold p := by
    have hBpos : 0 < (B_boot p : ℝ) := Nat.cast_pos.mpr (B_boot_pos p)
    unfold rowFailureThreshold
    exact mul_pos (mul_pos (by norm_num) (sq_pos_of_pos hBpos))
      (Real.rpow_pos_of_pos (by norm_num) _)
  have hBnonneg : 0 ≤ (B_boot p : ℝ) := by positivity
  have hpowNonneg : 0 ≤ (2 : ℝ) ^ (b_N p : ℝ) := by positivity
  have hpowSum : 0 ≤ (2 : ℝ) ^ (b_N p : ℝ) + (B_boot p : ℝ) :=
    add_nonneg hpowNonneg hBnonneg
  have hBsq : (B_boot p : ℝ) ^ 2 ≤ ((2 : ℝ) ^ (b_N p : ℝ)) ^ 2 := by
    have hproduct := mul_nonneg (sub_nonneg.mpr hBpow) hpowSum
    nlinarith
  have htailFactor : 0 ≤ (2 : ℝ) ^ (-8 * (b_N p : ℝ)) := by positivity
  have hscaled : rowFailureThreshold p ≤
      2 * ((2 : ℝ) ^ (b_N p : ℝ)) ^ 2 *
        (2 : ℝ) ^ (-8 * (b_N p : ℝ)) := by
    unfold rowFailureThreshold
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hBsq (by norm_num)) htailFactor
  have hpowSquare : ((2 : ℝ) ^ (b_N p : ℝ)) ^ 2 =
      (2 : ℝ) ^ (2 * (b_N p : ℝ)) := by
    calc
      ((2 : ℝ) ^ (b_N p : ℝ)) ^ 2 =
          ((2 : ℝ) ^ (b_N p : ℝ)) ^ (2 : ℝ) :=
            (Real.rpow_natCast ((2 : ℝ) ^ (b_N p : ℝ)) 2).symm
      _ = (2 : ℝ) ^ ((b_N p : ℝ) * 2) :=
        (Real.rpow_mul (by norm_num : 0 ≤ (2 : ℝ)) _ _).symm
      _ = (2 : ℝ) ^ (2 * (b_N p : ℝ)) := by congr 1; ring
  have hpowCombine :
      2 * ((2 : ℝ) ^ (b_N p : ℝ)) ^ 2 * (2 : ℝ) ^ (-8 * (b_N p : ℝ)) =
        (2 : ℝ) ^ (1 - 6 * (b_N p : ℝ)) := by
    rw [hpowSquare]
    calc
      2 * (2 : ℝ) ^ (2 * (b_N p : ℝ)) *
          (2 : ℝ) ^ (-8 * (b_N p : ℝ)) =
        (2 : ℝ) ^ (1 : ℝ) * (2 : ℝ) ^ (2 * (b_N p : ℝ)) *
          (2 : ℝ) ^ (-8 * (b_N p : ℝ)) := by
            exact congrArg (fun q : ℝ => q * (2 : ℝ) ^ (2 * (b_N p : ℝ)) *
              (2 : ℝ) ^ (-8 * (b_N p : ℝ))) (Real.rpow_one (2 : ℝ)).symm
      _ = (2 : ℝ) ^ (1 + 2 * (b_N p : ℝ)) *
          (2 : ℝ) ^ (-8 * (b_N p : ℝ)) := by
            rw [← Real.rpow_add (by norm_num : 0 < (2 : ℝ))]
      _ = (2 : ℝ) ^ (1 + 2 * (b_N p : ℝ) + (-8 * (b_N p : ℝ))) := by
            rw [← Real.rpow_add (by norm_num : 0 < (2 : ℝ))]
      _ = (2 : ℝ) ^ (1 - 6 * (b_N p : ℝ)) := by congr 1; ring
  have hpowLower : (2 : ℝ) ^ (1 - 6 * (b_N p : ℝ)) ≤
      (2 : ℝ) ^ (-5 * (b_N p : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith)
  have hp0le : rowFailureThreshold p ≤ (2 : ℝ) ^ (-5 * (b_N p : ℝ)) :=
    hscaled.trans (hpowCombine ▸ hpowLower)
  have hpowSmall : (2 : ℝ) ^ (-5 * (b_N p : ℝ)) ≤ (2 : ℝ) ^ (-5 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith)
  have hqquarter : (2 : ℝ) ^ (-5 * (b_N p : ℝ)) < (1 / 4 : ℝ) := by
    calc
      (2 : ℝ) ^ (-5 * (b_N p : ℝ)) ≤ (2 : ℝ) ^ (-5 : ℝ) := hpowSmall
      _ < 1 / 4 := by norm_num
  have hlog2lower : (2 : ℝ) / 3 ≤ Real.log 2 := by
    have h := Real.log_two_gt_d9
    norm_num at h ⊢
    linarith
  have hp0log : Real.log (rowFailureThreshold p) ≤
      -5 * (b_N p : ℝ) * Real.log 2 := by
    calc
      Real.log (rowFailureThreshold p) ≤
          Real.log ((2 : ℝ) ^ (-5 * (b_N p : ℝ))) :=
        Real.log_le_log hp0 hp0le
      _ = -5 * (b_N p : ℝ) * Real.log 2 := by rw [Real.log_rpow (by norm_num)]
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hlogDen : Real.log (4 * Real.exp 1 * rowFailureThreshold p) =
      2 * Real.log 2 + 1 + Real.log (rowFailureThreshold p) := by
    rw [Real.log_mul (by positivity) hp0.ne',
      Real.log_mul (by norm_num) (Real.exp_ne_zero 1), Real.log_exp, hlog4]
  have hnum : 2 * (b_N p : ℝ) ≤
      (5 * (b_N p : ℝ) - 2) * Real.log 2 - 1 := by
    have hcoef : 0 ≤ 5 * (b_N p : ℝ) - 2 := by linarith
    have hproduct := mul_le_mul_of_nonneg_left hlog2lower hcoef
    nlinarith [hproduct]
  have hlogtarget : 2 * (b_N p : ℝ) ≤
      Real.log (1 / (4 * Real.exp 1 * rowFailureThreshold p)) := by
    rw [show 1 / (4 * Real.exp 1 * rowFailureThreshold p) =
      (4 * Real.exp 1 * rowFailureThreshold p)⁻¹ by ring, Real.log_inv]
    rw [hlogDen]
    nlinarith [hnum, hp0log]
  exact ⟨hp0, hp0le, hqquarter, hlogtarget⟩

/-- The subtype of supports on a block has exactly the literal powerset size;
this includes the empty support and uses the actual clipped block carrier. -/
theorem blockSupport_card (p : Parameters) (s : Fin (n_boot p)) :
    Fintype.card (BlockSupport p s) = 2 ^ (calendarBlock p s).card := by
  classical
  let supports := (calendarBlock p s).powerset
  let equiv : BlockSupport p s ≃ {y // y ∈ supports} := {
    toFun := fun x => ⟨x.1, Finset.mem_powerset.mpr x.2⟩
    invFun := fun y => ⟨y.1, Finset.mem_powerset.mp y.2⟩
    left_inv := by intro x; cases x; rfl
    right_inv := by intro y; cases y; rfl }
  calc
    Fintype.card (BlockSupport p s) = Fintype.card {y // y ∈ supports} :=
      Fintype.card_congr equiv
    _ = supports.card := Fintype.card_coe supports
    _ = 2 ^ (calendarBlock p s).card := by simp [supports, Finset.card_powerset]

/-- The actual fixed-block, fixed-support failure probability is bounded by the
source exponential after complementing the accepted row events and applying
`independentRareEventCount_oneQuarter`. -/
theorem propertyIIIFixedSupport_failure_probability_le (p : Parameters)
    (s : Fin (n_boot p)) (x : BlockSupport p s) :
    (idArrayMeasure p).real (propertyIIIFixedSupportFailureEvent p s x) ≤
      Real.exp (-((A_id p : ℝ) * (b_N p : ℝ) / 2)) := by
  classical
  let badRow : Fin (A_id p) → Set (IDArray p) :=
    fun u => (localBalanceRowEvent p s x u)ᶜ
  have hbadMeas : ∀ u, MeasurableSet (badRow u) := by
    intro u
    exact (measurableSet_localBalanceRowEvent p s x u).compl
  have hbadIndep : iIndepSet badRow (idArrayMeasure p) := by
    apply (iIndepSet_iff_iIndep badRow (idArrayMeasure p)).mpr
    have hgood : iIndep (fun u : Fin (A_id p) =>
        MeasurableSpace.generateFrom {localBalanceRowEvent p s x u})
          (idArrayMeasure p) :=
      (iIndepSet_iff_iIndep (fun u : Fin (A_id p) =>
        localBalanceRowEvent p s x u) (idArrayMeasure p)).mp
          (iIndepSet_localBalanceRowEvent p s x)
    have hgen (u : Fin (A_id p)) :
        MeasurableSpace.generateFrom {localBalanceRowEvent p s x u} =
          MeasurableSpace.generateFrom {badRow u} := by
      apply le_antisymm
      · apply MeasurableSpace.generateFrom_le
        intro t ht
        have htEq : t = localBalanceRowEvent p s x u := Set.mem_singleton_iff.mp ht
        subst t
        simpa [badRow] using
          (MeasurableSpace.measurableSet_generateFrom (show
            (localBalanceRowEvent p s x u)ᶜ ∈ {badRow u} by simp [badRow])).compl
      · apply MeasurableSpace.generateFrom_le
        intro t ht
        have htEq : t = badRow u := Set.mem_singleton_iff.mp ht
        subst t
        simpa [badRow] using
          (MeasurableSpace.measurableSet_generateFrom (show
            localBalanceRowEvent p s x u ∈ {localBalanceRowEvent p s x u} by simp)).compl
    have hspaces :
        (fun u : Fin (A_id p) => MeasurableSpace.generateFrom {badRow u}) =
          (fun u : Fin (A_id p) =>
            MeasurableSpace.generateFrom {localBalanceRowEvent p s x u}) := by
      funext u
      exact (hgen u).symm
    rw [hspaces]
    exact hgood
  rcases rowFailureThreshold_bounds p with ⟨hp0pos, hp0le, hqquarter, hlog⟩
  have hp0quarter : rowFailureThreshold p < (1 / 4 : ℝ) := hp0le.trans_lt hqquarter
  have hprob : ∀ u, (idArrayMeasure p).real (badRow u) ≤ rowFailureThreshold p := by
    intro u
    exact (localBalanceRowEvent_failure_probability_le p s x u).trans_eq rfl
  have hcard : 0 < Fintype.card (Fin (A_id p)) := by
    simp only [Fintype.card_fin]
    exact A_id_pos p
  have htail := RareTailBound.independentRareEventCount_oneQuarter
    (idArrayMeasure p) badRow hbadMeas hbadIndep (rowFailureThreshold p)
    hp0pos hp0quarter hprob hcard
  have hgoodSum (id : IDArray p) :
      (∑ u : Fin (A_id p),
        (localBalanceRowEvent p s x u).indicator (fun _ : IDArray p => (1 : ℝ)) id) =
        (propertyIIIGoodRowCount p id s x : ℝ) := by
    change (∑ u : Fin (A_id p), if id ∈ localBalanceRowEvent p s x u then
      (1 : ℝ) else 0) = _
    simp [propertyIIIGoodRowCount, Finset.sum_boole]
  have hbadGoodSum (id : IDArray p) :
      (∑ u : Fin (A_id p), (badRow u).indicator
        (fun _ : IDArray p => (1 : ℝ)) id) +
        (propertyIIIGoodRowCount p id s x : ℝ) = (A_id p : ℝ) := by
    rw [← hgoodSum]
    rw [← Finset.sum_add_distrib]
    calc
      (∑ u : Fin (A_id p),
          ((badRow u).indicator (fun _ : IDArray p => (1 : ℝ)) id +
            (localBalanceRowEvent p s x u).indicator
              (fun _ : IDArray p => (1 : ℝ)) id)) =
          ∑ _u : Fin (A_id p), (1 : ℝ) := by
            apply Finset.sum_congr rfl
            intro u hu
            by_cases hmem : id ∈ localBalanceRowEvent p s x u <;>
              simp [badRow, Set.indicator, hmem]
      _ = (A_id p : ℝ) := by simp
  have hbadEq (id : IDArray p) :
      (∑ u : Fin (A_id p), (badRow u).indicator
        (fun _ : IDArray p => (1 : ℝ)) id) =
          (A_id p : ℝ) - (propertyIIIGoodRowCount p id s x : ℝ) := by
    linarith [hbadGoodSum id]
  have hcountEquivalent (id : IDArray p) :
      (propertyIIIGoodRowCount p id s x : ℝ) <
          (3 * (A_id p : ℝ)) / 4 ↔
        (1 / 4 : ℝ) <
          (∑ u : Fin (A_id p), (badRow u).indicator
            (fun _ : IDArray p => (1 : ℝ)) id) /
            (Fintype.card (Fin (A_id p)) : ℝ) := by
    rw [hbadEq id]
    simp only [Fintype.card_fin]
    have hApos : 0 < (A_id p : ℝ) := Nat.cast_pos.mpr (A_id_pos p)
    rw [lt_div_iff₀ hApos]
    constructor <;> intro h <;> nlinarith
  have hset : propertyIIIFixedSupportFailureEvent p s x =
      {id | (1 / 4 : ℝ) <
        (∑ u : Fin (A_id p), (badRow u).indicator
          (fun _ : IDArray p => (1 : ℝ)) id) /
          (Fintype.card (Fin (A_id p)) : ℝ)} := by
    ext id
    exact hcountEquivalent id
  rw [hset]
  have hlogArgEq :
      (1 / 4 : ℝ) / (Real.exp 1 * rowFailureThreshold p) =
        1 / (4 * Real.exp 1 * rowFailureThreshold p) := by
    field_simp [hp0pos.ne', Real.exp_ne_zero]
  have hlogTail : 2 * (b_N p : ℝ) ≤
      Real.log ((1 / 4 : ℝ) / (Real.exp 1 * rowFailureThreshold p)) := by
    rw [hlogArgEq]
    exact hlog
  have htailExponent :
      -((Fintype.card (Fin (A_id p)) : ℝ) * (1 / 4 : ℝ)) *
          Real.log ((1 / 4 : ℝ) / (Real.exp 1 * rowFailureThreshold p)) ≤
        -((A_id p : ℝ) * (b_N p : ℝ) / 2) := by
    simp only [Fintype.card_fin]
    have hA_nonneg : 0 ≤ (A_id p : ℝ) := Nat.cast_nonneg _
    have hmul := mul_le_mul_of_nonneg_left hlogTail
      (by positivity : 0 ≤ (A_id p : ℝ) / 4)
    nlinarith [hmul]
  exact htail.trans (Real.exp_le_exp.mpr htailExponent)

/-- On the construction branch, the literal property (iii) failure event has
probability at most `1 / N`. The only branch hypotheses are the source's
universal `C_b ≥ 16` and strict horizon inequality; source: the ranges above.
-/
theorem propertyIII_failure_probability_le (C_b : ℝ) (p : Parameters)
    (hCb : 16 ≤ C_b)
    (hbranch : C_b * (p.m : ℝ) * (p.K : ℝ) * (b_N p : ℝ) ^ 2 < (p.T : ℝ)) :
    (idArrayMeasure p).real (propertyIIIFailureEvent p) ≤
      (1 : ℝ) / (N p : ℝ) := by
  classical
  have hm : 2 ≤ (p.m : ℝ) := by exact_mod_cast p.two_le_m
  have hKnat : 3 ≤ p.K :=
    Nat.succ_le_of_lt (lt_of_le_of_lt p.two_le_m p.m_lt_K)
  have hK : 3 ≤ (p.K : ℝ) := by exact_mod_cast hKnat
  have hbposNat : 0 < b_N p := b_N_pos p
  have hbgeNat : 1 ≤ b_N p := Nat.succ_le_of_lt hbposNat
  have hbge : 1 ≤ (b_N p : ℝ) := by exact_mod_cast hbgeNat
  have hCbMK : 96 ≤ C_b * (p.m : ℝ) * (p.K : ℝ) := by
    have hCb2 : C_b * 2 ≤ C_b * (p.m : ℝ) :=
      mul_le_mul_of_nonneg_left hm (by linarith)
    calc
      96 = 16 * 2 * 3 := by norm_num
      _ ≤ C_b * 2 * 3 := by nlinarith [hCb]
      _ ≤ C_b * (p.m : ℝ) * 3 := by
        have h := mul_le_mul_of_nonneg_right hCb2 (by norm_num : (0 : ℝ) ≤ 3)
        nlinarith [h]
      _ ≤ C_b * (p.m : ℝ) * (p.K : ℝ) := by
        have h := mul_le_mul_of_nonneg_left hK (by positivity :
          (0 : ℝ) ≤ C_b * (p.m : ℝ))
        nlinarith [h]
  have hbranchTerm : 96 ≤
      C_b * (p.m : ℝ) * (p.K : ℝ) * (b_N p : ℝ) ^ 2 := by
    have hbSq : 1 ≤ (b_N p : ℝ) ^ 2 := by
      nlinarith [sq_nonneg ((b_N p : ℝ) - 1)]
    have hmul := mul_le_mul hCbMK hbSq (by norm_num : (0 : ℝ) ≤ 1)
      (by positivity : (0 : ℝ) ≤ C_b * (p.m : ℝ) * (p.K : ℝ))
    nlinarith [hmul]
  have hT4 : 4 ≤ (p.T : ℝ) := by linarith [lt_of_le_of_lt hbranchTerm hbranch]
  have hdim := propertyIII_dimension_estimates p
  have hTleN : p.T ≤ N p := horizon_le_source_size p
  have hNpos : 0 < (N p : ℝ) := Nat.cast_pos.mpr (N_pos p)
  have hApos : 0 < (A_id p : ℝ) := Nat.cast_pos.mpr (A_id_pos p)
  have hBnonneg : 0 ≤ (B_boot p : ℝ) := Nat.cast_nonneg _
  have hbn_nonneg : 0 ≤ (b_N p : ℝ) := Nat.cast_nonneg _
  have hAblarge :
      (p.T : ℝ) * ((B_boot p : ℝ) + (b_N p : ℝ)) ≤
        (A_id p : ℝ) * (b_N p : ℝ) := by
    have hnat := T_mul_boot_plus_b_N_le_A_id_mul_b_N p
    exact_mod_cast hnat
  have hmainExponent :
      2 * ((B_boot p : ℝ) + (b_N p : ℝ)) ≤
        (A_id p : ℝ) * (b_N p : ℝ) / 2 := by
    have hmul := mul_le_mul_of_nonneg_right hT4
      (add_nonneg hBnonneg hbn_nonneg)
    nlinarith [hAblarge]
  have hlog2le : Real.log 2 ≤ 1 := by
    calc
      Real.log 2 ≤ 2 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
      _ = 1 := by norm_num
  have hlogNle : Real.log (N p : ℝ) ≤ (b_N p : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left hlog2le hbn_nonneg
    simpa only [mul_one] using hdim.2.2.2.trans hmul
  have hBcastNonneg : 0 ≤ (B_boot p : ℝ) := hBnonneg
  have hpowExp : (2 : ℝ) ^ B_boot p =
      Real.exp ((B_boot p : ℝ) * Real.log 2) := by
    calc
      (2 : ℝ) ^ B_boot p = (Real.exp (Real.log 2)) ^ B_boot p := by
        rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      _ = Real.exp ((B_boot p : ℝ) * Real.log 2) := by
        rw [← Real.exp_nat_mul]
  have hNexp : (N p : ℝ) = Real.exp (Real.log (N p : ℝ)) :=
    (Real.exp_log hNpos).symm
  have hexpUnion :
      (N p : ℝ) * (2 : ℝ) ^ B_boot p *
          Real.exp (-2 * ((B_boot p : ℝ) + (b_N p : ℝ))) ≤
        (1 : ℝ) / (N p : ℝ) := by
    have hlogPower : (B_boot p : ℝ) * Real.log 2 ≤ (B_boot p : ℝ) := by
      have hmul := mul_le_mul_of_nonneg_left hlog2le hBcastNonneg
      simpa only [mul_one] using hmul
    have hexponent :
        Real.log (N p : ℝ) + (B_boot p : ℝ) * Real.log 2 -
            2 * ((B_boot p : ℝ) + (b_N p : ℝ)) ≤
          -Real.log (N p : ℝ) := by
      nlinarith [hlogNle, hlogPower]
    have hleft :
        (N p : ℝ) * (2 : ℝ) ^ B_boot p *
            Real.exp (-2 * ((B_boot p : ℝ) + (b_N p : ℝ))) =
          Real.exp (Real.log (N p : ℝ) + (B_boot p : ℝ) * Real.log 2 -
            2 * ((B_boot p : ℝ) + (b_N p : ℝ))) := by
      calc
        (N p : ℝ) * (2 : ℝ) ^ B_boot p *
            Real.exp (-2 * ((B_boot p : ℝ) + (b_N p : ℝ))) =
          Real.exp (Real.log (N p : ℝ)) *
            Real.exp ((B_boot p : ℝ) * Real.log 2) *
              Real.exp (-2 * ((B_boot p : ℝ) + (b_N p : ℝ))) := by
                conv_lhs => rw [hNexp, hpowExp]
        _ = Real.exp (Real.log (N p : ℝ) + (B_boot p : ℝ) * Real.log 2 -
            2 * ((B_boot p : ℝ) + (b_N p : ℝ))) := by
              rw [← Real.exp_add, ← Real.exp_add]
              congr 1
              ring
    calc
      (N p : ℝ) * (2 : ℝ) ^ B_boot p *
          Real.exp (-2 * ((B_boot p : ℝ) + (b_N p : ℝ))) =
        Real.exp (Real.log (N p : ℝ) + (B_boot p : ℝ) * Real.log 2 -
          2 * ((B_boot p : ℝ) + (b_N p : ℝ))) := hleft
      _ ≤ Real.exp (-Real.log (N p : ℝ)) := Real.exp_le_exp.mpr hexponent
      _ = (1 : ℝ) / (N p : ℝ) := by
        rw [Real.exp_neg, Real.exp_log hNpos]
        ring
  let index := Σ s : Fin (n_boot p), BlockSupport p s
  have hindexCard : Fintype.card index ≤ n_boot p * 2 ^ B_boot p := by
    rw [Fintype.card_sigma]
    calc
      (∑ s : Fin (n_boot p), Fintype.card (BlockSupport p s)) ≤
          ∑ s : Fin (n_boot p), 2 ^ B_boot p := by
        apply Finset.sum_le_sum
        intro s hs
        rw [blockSupport_card]
        exact pow_le_pow_right' (by decide : 1 ≤ 2)
          (calendarBlock_card_le_B_boot p s)
      _ = n_boot p * 2 ^ B_boot p := by simp
  have hGlobalEq : propertyIIIFailureEvent p =
      ⋃ ix : index, propertyIIIFixedSupportFailureEvent p ix.1 ix.2 := by
    ext id
    simp only [propertyIIIFailureEvent, propertyIII, propertyIIIFixedSupportFailureEvent,
      Set.mem_ofPred_eq, Set.mem_iUnion, not_forall, not_le]
    constructor
    · rintro ⟨s, x, hx⟩
      exact ⟨⟨s, x⟩, hx⟩
    · rintro ⟨⟨s, x⟩, hx⟩
      exact ⟨s, x, hx⟩
  have hfixedBound (ix : index) :
      (idArrayMeasure p).real
          (propertyIIIFixedSupportFailureEvent p ix.1 ix.2) ≤
        Real.exp (-((A_id p : ℝ) * (b_N p : ℝ) / 2)) :=
    propertyIIIFixedSupport_failure_probability_le p ix.1 ix.2
  have hunion := measureReal_iUnion_fintype_le
    (μ := idArrayMeasure p)
    (fun ix : index => propertyIIIFixedSupportFailureEvent p ix.1 ix.2)
  have hsum :
      (∑ ix : index,
        (idArrayMeasure p).real
          (propertyIIIFixedSupportFailureEvent p ix.1 ix.2)) ≤
        (Fintype.card index : ℝ) *
          Real.exp (-((A_id p : ℝ) * (b_N p : ℝ) / 2)) := by
    calc
      _ ≤ ∑ ix : index, Real.exp (-((A_id p : ℝ) * (b_N p : ℝ) / 2)) :=
        Finset.sum_le_sum fun ix _ => hfixedBound ix
      _ = _ := by simp
  have hcountReal : (Fintype.card index : ℝ) ≤
      (n_boot p : ℝ) * (2 : ℝ) ^ B_boot p := by
    exact_mod_cast hindexCard
  have hblocksReal : (n_boot p : ℝ) ≤ (N p : ℝ) := by exact_mod_cast hdim.1
  have htotal :
      (Fintype.card index : ℝ) *
          Real.exp (-((A_id p : ℝ) * (b_N p : ℝ) / 2)) ≤
        (N p : ℝ) * (2 : ℝ) ^ B_boot p *
          Real.exp (-2 * ((B_boot p : ℝ) + (b_N p : ℝ))) := by
    have hexpBound :
        Real.exp (-((A_id p : ℝ) * (b_N p : ℝ) / 2)) ≤
          Real.exp (-2 * ((B_boot p : ℝ) + (b_N p : ℝ))) := by
      apply Real.exp_le_exp.mpr
      nlinarith [hmainExponent]
    calc
      (Fintype.card index : ℝ) *
          Real.exp (-((A_id p : ℝ) * (b_N p : ℝ) / 2)) ≤
        ((n_boot p : ℝ) * (2 : ℝ) ^ B_boot p) *
          Real.exp (-((A_id p : ℝ) * (b_N p : ℝ) / 2)) :=
            mul_le_mul_of_nonneg_right hcountReal (Real.exp_nonneg _)
      _ ≤ ((N p : ℝ) * (2 : ℝ) ^ B_boot p) *
          Real.exp (-((A_id p : ℝ) * (b_N p : ℝ) / 2)) := by
            gcongr
      _ ≤ ((N p : ℝ) * (2 : ℝ) ^ B_boot p) *
          Real.exp (-2 * ((B_boot p : ℝ) + (b_N p : ℝ))) := by
            exact mul_le_mul_of_nonneg_left hexpBound (by positivity)
      _ = _ := by ring
  rw [hGlobalEq]
  calc
    (idArrayMeasure p).real
        (⋃ ix : index, propertyIIIFixedSupportFailureEvent p ix.1 ix.2) ≤
        ∑ ix : index,
          (idArrayMeasure p).real
            (propertyIIIFixedSupportFailureEvent p ix.1 ix.2) := hunion
    _ ≤ (Fintype.card index : ℝ) *
          Real.exp (-((A_id p : ℝ) * (b_N p : ℝ) / 2)) := hsum
    _ ≤ (N p : ℝ) * (2 : ℝ) ^ B_boot p *
          Real.exp (-2 * ((B_boot p : ℝ) + (b_N p : ℝ))) := htotal
    _ ≤ (1 : ℝ) / (N p : ℝ) := hexpUnion

end Bandits.Support.IdentificationBlockBalance

end
