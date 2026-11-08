/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.BootstrapDimensions
public import Bandits.Support.CompletePublicTable

import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Column balance of the identification array

The fair, independent ID bits imply that every column has at least one third
of its rows of either bit, except with probability at most `1 / N` on the
construction branch.  This is property (i) of the identification-array event.
Sources: `sources/zip4/manuscript/appendix_b_communication.tex:195-207` and
`sources/zip4/manuscript/07_public_setup.tex:5-25`.
-/

public section

open MeasureTheory ProbabilityTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.CompletePublicTable

namespace Bandits.Support.IdentificationColumnBalance

/-- Literal source event: in every time column, each bit occurs in at least
one third of the identification rows. Source:
`sources/zip4/manuscript/appendix_b_communication.tex:195-200`. -/
@[expose] noncomputable def columnBalanced (p : ConstructorDimensions.Parameters)
    (id : CompletePublicTable.IDArray p) : Prop :=
  ∀ t : Fin p.T, ∀ e : Bool,
    (BootstrapDimensions.A_id p : ℝ) / 3 ≤
      ((Finset.univ.filter (fun u : Fin (BootstrapDimensions.A_id p) => id u t = e)).card : ℝ)

/-- The centered indicator for one prescribed bit in a fixed ID column. -/
@[expose] noncomputable def idColumnCentered (p : ConstructorDimensions.Parameters) (t : Fin p.T)
    (e : Bool) (u : Fin (BootstrapDimensions.A_id p))
    (id : CompletePublicTable.IDArray p) : ℝ :=
  if idCoordinate p u t id = e then -(1 / 2 : ℝ) else (1 / 2 : ℝ)

/-- The strict source construction-branch horizon inequality, with the
universal constant kept separate from the constructor parameters. Source:
`sources/zip4/manuscript/07_public_setup.tex:5-9`. -/
@[expose] def constructionBranchBound (C_b : ℝ) (p : ConstructorDimensions.Parameters) : Prop :=
  C_b * (p.m : ℝ) * (p.K : ℝ) * (ConstructorDimensions.b_N p : ℝ) ^ 2 < (p.T : ℝ)

/-- The construction-branch lower bound yields the logarithmic horizon bound;
the accepted constructor and bootstrap dimensions supply the other two bounds
used in the column union bound. -/
theorem construction_branch_dimensions (C_b : ℝ) (p : ConstructorDimensions.Parameters)
    (hCb : 16 ≤ C_b) (hbranch : constructionBranchBound C_b p) :
    36 * Real.log (ConstructorDimensions.N p : ℝ) ≤ (p.T : ℝ) ∧
      p.T ≤ BootstrapDimensions.A_id p ∧ 2 * p.T ≤ ConstructorDimensions.N p := by
  have hmK_nat : 6 ≤ p.m * p.K := by
    have hK : 3 ≤ p.K :=
      Nat.succ_le_of_lt (lt_of_le_of_lt p.two_le_m p.m_lt_K)
    calc
      6 = 2 * 3 := by norm_num
      _ ≤ p.m * p.K := Nat.mul_le_mul p.two_le_m hK
  have hmK : (6 : ℝ) ≤ (p.m : ℝ) * (p.K : ℝ) := by
    exact_mod_cast hmK_nat
  have hb_pos_nat : 0 < ConstructorDimensions.b_N p :=
    ConstructorDimensions.b_N_pos p
  have hb_ge_one : (1 : ℝ) ≤ (ConstructorDimensions.b_N p : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt hb_pos_nat
  have hCbMK : (96 : ℝ) ≤ C_b * (p.m : ℝ) * (p.K : ℝ) := by
    calc
      96 = 16 * 6 := by norm_num
      _ ≤ C_b * 6 := mul_le_mul_of_nonneg_right hCb (by norm_num)
      _ ≤ C_b * ((p.m : ℝ) * (p.K : ℝ)) :=
        mul_le_mul_of_nonneg_left hmK (by linarith)
      _ = C_b * (p.m : ℝ) * (p.K : ℝ) := by ring
  have hCbMKb :
      96 * (ConstructorDimensions.b_N p : ℝ) ^ 2 ≤
        C_b * (p.m : ℝ) * (p.K : ℝ) * (ConstructorDimensions.b_N p : ℝ) ^ 2 :=
    mul_le_mul_of_nonneg_right hCbMK (sq_nonneg _)
  have hT96 :
      96 * (ConstructorDimensions.b_N p : ℝ) ^ 2 < (p.T : ℝ) :=
    lt_of_le_of_lt hCbMKb hbranch
  have hlog2 : Real.log 2 ≤ 1 := by
    calc
      Real.log 2 ≤ 2 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
      _ = 1 := by norm_num
  have hN_pos : 0 < (ConstructorDimensions.N p : ℝ) :=
    Nat.cast_pos.mpr (ConstructorDimensions.N_pos p)
  have hND : (ConstructorDimensions.N p : ℝ) < (ConstructorDimensions.D p : ℝ) := by
    exact_mod_cast ConstructorDimensions.N_lt_D p
  have hlogD :
      Real.log (ConstructorDimensions.D p : ℝ) =
        (ConstructorDimensions.b_N p : ℝ) * Real.log 2 := by
    simp only [ConstructorDimensions.D, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
  have hlogN_lt :
      Real.log (ConstructorDimensions.N p : ℝ) <
        (ConstructorDimensions.b_N p : ℝ) := by
    calc
      Real.log (ConstructorDimensions.N p : ℝ) <
          Real.log (ConstructorDimensions.D p : ℝ) := Real.log_lt_log hN_pos hND
      _ = (ConstructorDimensions.b_N p : ℝ) * Real.log 2 := hlogD
      _ ≤ ConstructorDimensions.b_N p := by
        calc
          (ConstructorDimensions.b_N p : ℝ) * Real.log 2 ≤
              (ConstructorDimensions.b_N p : ℝ) * 1 :=
            mul_le_mul_of_nonneg_left hlog2 (Nat.cast_nonneg _)
          _ = ConstructorDimensions.b_N p := by ring
  have hlogN :
      Real.log (ConstructorDimensions.N p : ℝ) ≤
        (ConstructorDimensions.b_N p : ℝ) := hlogN_lt.le
  have h36b :
      36 * (ConstructorDimensions.b_N p : ℝ) ≤
        96 * (ConstructorDimensions.b_N p : ℝ) ^ 2 := by
    nlinarith [hb_ge_one]
  have hTlog : 36 * Real.log (ConstructorDimensions.N p : ℝ) < (p.T : ℝ) := by
    calc
      36 * Real.log (ConstructorDimensions.N p : ℝ) ≤
          36 * (ConstructorDimensions.b_N p : ℝ) :=
        mul_le_mul_of_nonneg_left hlogN (by norm_num)
      _ ≤ 96 * (ConstructorDimensions.b_N p : ℝ) ^ 2 := h36b
      _ < (p.T : ℝ) := hT96
  have hA : p.T ≤ BootstrapDimensions.A_id p :=
    BootstrapDimensions.T_le_A_id p
  have h2TN_nat : 2 * p.T ≤ ConstructorDimensions.N p := by
    have hmK_one : 1 ≤ p.m * p.K := by
      have hm : 1 ≤ p.m := Nat.le_trans (by decide) p.two_le_m
      have hK : 1 ≤ p.K := Nat.le_trans hm (Nat.le_of_lt p.m_lt_K)
      calc
        1 = 1 * 1 := by norm_num
        _ ≤ p.m * p.K := Nat.mul_le_mul hm hK
    have hTle : p.T ≤ p.m * p.K * (p.T + 1) := by
      calc
        p.T ≤ p.T + 1 := Nat.le_succ _
        _ = 1 * (p.T + 1) := by simp
        _ ≤ p.m * p.K * (p.T + 1) :=
          Nat.mul_le_mul_right (p.T + 1) hmK_one
    calc
      2 * p.T ≤ 2 * (p.m * p.K * (p.T + 1)) := Nat.mul_le_mul_left 2 hTle
      _ = ConstructorDimensions.N p := by
        simp [ConstructorDimensions.N, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  refine ⟨hTlog.le, hA, ?_⟩
  exact_mod_cast h2TN_nat

private theorem idColumnCentered_integral_eq_zero
    (p : ConstructorDimensions.Parameters) (t : Fin p.T) (e : Bool)
    (u : Fin (BootstrapDimensions.A_id p)) :
    ∫ id, idColumnCentered p t e u id ∂idArrayMeasure p = 0 := by
  let μ := idArrayMeasure p
  let s : Set (IDArray p) := {id | idCoordinate p u t id = e}
  have hs : MeasurableSet s := by
    exact (measurable_idCoordinate p u t) (measurableSet_singleton e)
  have hmass : μ.real s = (1 / 2 : ℝ) := by
    cases e with
    | false => simpa [s] using idCoordinate_false_mass p u t
    | true => simpa [s] using idCoordinate_true_mass p u t
  have hmass_compl : μ.real sᶜ = (1 / 2 : ℝ) := by
    rw [measureReal_compl hs]
    have hμuniv : μ.real Set.univ = 1 := by simp [μ]
    rw [hμuniv, hmass]
    norm_num
  have hsignal :
      idColumnCentered p t e u =
        s.indicator (fun _ : IDArray p => -(1 / 2 : ℝ)) +
          sᶜ.indicator (fun _ : IDArray p => (1 / 2 : ℝ)) := by
    funext id
    by_cases hid : idCoordinate p u t id = e <;>
      simp [idColumnCentered, s, hid]
  have hneg_meas :
      Measurable (s.indicator (fun _ : IDArray p => -(1 / 2 : ℝ))) :=
    measurable_const.indicator hs
  have hpos_meas :
      Measurable (sᶜ.indicator (fun _ : IDArray p => (1 / 2 : ℝ))) :=
    measurable_const.indicator hs.compl
  have hneg_bound :
      ∀ id, s.indicator (fun _ : IDArray p => -(1 / 2 : ℝ)) id ∈ Set.Icc (-(1 / 2 : ℝ)) 0 := by
    intro id
    by_cases hid : id ∈ s
    · simp [hid]
    · simp [hid]
  have hpos_bound :
      ∀ id, sᶜ.indicator (fun _ : IDArray p => (1 / 2 : ℝ)) id ∈ Set.Icc 0 (1 / 2 : ℝ) := by
    intro id
    by_cases hid : id ∈ sᶜ
    · simp [hid]
    · simp [hid]
  have hneg_int :
      Integrable (s.indicator (fun _ : IDArray p => -(1 / 2 : ℝ))) μ :=
    Integrable.of_mem_Icc _ _ hneg_meas.aemeasurable (ae_of_all _ hneg_bound)
  have hpos_int :
      Integrable (sᶜ.indicator (fun _ : IDArray p => (1 / 2 : ℝ))) μ :=
    Integrable.of_mem_Icc _ _ hpos_meas.aemeasurable (ae_of_all _ hpos_bound)
  calc
    ∫ id, idColumnCentered p t e u id ∂idArrayMeasure p =
        ∫ id, (s.indicator (fun _ : IDArray p => -(1 / 2 : ℝ)) +
          sᶜ.indicator (fun _ : IDArray p => (1 / 2 : ℝ))) id ∂μ := by rw [hsignal]
    _ = (∫ id, s.indicator (fun _ : IDArray p => -(1 / 2 : ℝ)) id ∂μ) +
        ∫ id, sᶜ.indicator (fun _ : IDArray p => (1 / 2 : ℝ)) id ∂μ :=
      integral_add hneg_int hpos_int
    _ = 0 := by
      rw [integral_indicator_const _ hs, integral_indicator_const _ hs.compl]
      rw [hmass, hmass_compl]
      norm_num

/-- Each fixed column and prescribed bit fails its one-third balance threshold
with probability at most the Hoeffding bound `exp (-A_id / 18)`. -/
theorem idArray_column_failure_measure_le (p : ConstructorDimensions.Parameters)
    (t : Fin p.T) (e : Bool) :
    (idArrayMeasure p).real
      {id | ((Finset.univ.filter
        (fun u : Fin (BootstrapDimensions.A_id p) => id u t = e)).card : ℝ) <
          (BootstrapDimensions.A_id p : ℝ) / 3} ≤
      Real.exp (-(BootstrapDimensions.A_id p : ℝ) / 18) := by
  let μ := idArrayMeasure p
  let X : Fin (BootstrapDimensions.A_id p) → IDArray p → ℝ :=
    fun u id => idColumnCentered p t e u id
  let c : NNReal :=
    (‖(1 / 2 : ℝ) - (-(1 / 2 : ℝ))‖₊ / 2) ^ 2
  have hcoord :
      iIndepFun (fun u : Fin (BootstrapDimensions.A_id p) => idCoordinate p u t) μ := by
    apply (iIndepFun_idCoordinate p).precomp (g := fun u => (u, t))
    intro u v huv
    exact congrArg Prod.fst huv
  have hX_indep : iIndepFun X μ := by
    change iIndepFun (fun u : Fin (BootstrapDimensions.A_id p) =>
      fun id : IDArray p =>
        if idCoordinate p u t id = e then -(1 / 2 : ℝ) else (1 / 2 : ℝ)) μ
    exact hcoord.comp
      (fun _ : Fin (BootstrapDimensions.A_id p) =>
        fun b : Bool => if b = e then -(1 / 2 : ℝ) else (1 / 2 : ℝ))
      (by
        intro u
        fun_prop)
  have hX_meas (u : Fin (BootstrapDimensions.A_id p)) :
      Measurable (X u) := by
    change Measurable (fun id : IDArray p =>
      if idCoordinate p u t id = e then -(1 / 2 : ℝ) else (1 / 2 : ℝ))
    fun_prop
  have hX_bound (u : Fin (BootstrapDimensions.A_id p)) :
      ∀ᵐ id ∂μ, X u id ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ) := by
    filter_upwards [] with id
    simp only [X, idColumnCentered]
    split_ifs <;> norm_num
  have hX_subG (u : Fin (BootstrapDimensions.A_id p)) :
      HasSubgaussianMGF (X u) c μ := by
    have h := ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
      (hX_meas u).aemeasurable (hX_bound u)
      (idColumnCentered_integral_eq_zero p t e u)
    simpa [c, X, idColumnCentered] using h
  have hApos : 0 < BootstrapDimensions.A_id p := BootstrapDimensions.A_id_pos p
  have hε : 0 ≤ (BootstrapDimensions.A_id p : ℝ) / 6 := by positivity
  have htail := ProbabilityTheory.HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun
    hX_indep (s := Finset.univ) (fun u _ => hX_subG u) hε
  have hsum_identity (id : IDArray p) :
      (∑ u : Fin (BootstrapDimensions.A_id p), X u id) =
        (BootstrapDimensions.A_id p : ℝ) / 2 -
          ((Finset.univ.filter
            (fun u : Fin (BootstrapDimensions.A_id p) => id u t = e)).card : ℝ) := by
    calc
      (∑ u : Fin (BootstrapDimensions.A_id p), X u id) =
          ∑ u : Fin (BootstrapDimensions.A_id p),
            ((1 / 2 : ℝ) - if id u t = e then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro u hu
        simp only [X, idColumnCentered, idCoordinate]
        by_cases hmatch : id u t = e
        · simp [hmatch]
          ring
        · simp [hmatch]
      _ = (∑ _u : Fin (BootstrapDimensions.A_id p), (1 / 2 : ℝ)) -
          ∑ u : Fin (BootstrapDimensions.A_id p), if id u t = e then 1 else 0 :=
        by rw [Finset.sum_sub_distrib]
      _ = (BootstrapDimensions.A_id p : ℝ) / 2 -
          ((Finset.univ.filter
            (fun u : Fin (BootstrapDimensions.A_id p) => id u t = e)).card : ℝ) := by
        simp [Finset.sum_boole]
        ring
  have hsubset :
      {id | ((Finset.univ.filter
        (fun u : Fin (BootstrapDimensions.A_id p) => id u t = e)).card : ℝ) <
          (BootstrapDimensions.A_id p : ℝ) / 3} ⊆
        {id | (BootstrapDimensions.A_id p : ℝ) / 6 ≤ ∑ u : Fin (BootstrapDimensions.A_id p), X u id} := by
    intro id hid
    rw [Set.mem_ofPred_eq, hsum_identity]
    have hcount := hid
    change ((Finset.univ.filter
      (fun u : Fin (BootstrapDimensions.A_id p) => id u t = e)).card : ℝ) <
        (BootstrapDimensions.A_id p : ℝ) / 3 at hcount
    linarith
  have hsumc :
      ((∑ _u : Fin (BootstrapDimensions.A_id p), c : NNReal) : ℝ) =
        (BootstrapDimensions.A_id p : ℝ) / 4 := by
    have hsumc_nn :
        (∑ _u : Fin (BootstrapDimensions.A_id p), c) =
          (BootstrapDimensions.A_id p : NNReal) * c := by
      simp [Finset.sum_const, Finset.card_univ]
    have hwidth :
        (1 / 2 : ℝ) - (-(1 / 2 : ℝ)) = 1 := by norm_num
    have hwidth_nonneg :
        0 ≤ (1 / 2 : ℝ) - (-(1 / 2 : ℝ)) := by rw [hwidth]; norm_num
    have hcoef : (c : ℝ) = 1 / 4 := by
      change (((‖(1 / 2 : ℝ) - (-(1 / 2 : ℝ))‖₊ / 2) ^ 2 : NNReal) : ℝ) = _
      rw [NNReal.coe_pow, NNReal.coe_div, coe_nnnorm]
      rw [Real.norm_of_nonneg hwidth_nonneg, hwidth]
      norm_num
    rw [hsumc_nn, NNReal.coe_mul, hcoef]
    simp only [NNReal.coe_natCast]
    ring
  have hAne : (BootstrapDimensions.A_id p : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr hApos)
  have hexponent :
      -((BootstrapDimensions.A_id p : ℝ) / 6) ^ 2 /
          (2 * (∑ _u : Fin (BootstrapDimensions.A_id p), c)) =
        -(BootstrapDimensions.A_id p : ℝ) / 18 := by
    rw [hsumc]
    field_simp
    ring
  calc
    (idArrayMeasure p).real
        {id | ((Finset.univ.filter
          (fun u : Fin (BootstrapDimensions.A_id p) => id u t = e)).card : ℝ) <
            (BootstrapDimensions.A_id p : ℝ) / 3} ≤
      μ.real {id | (BootstrapDimensions.A_id p : ℝ) / 6 ≤ ∑ u : Fin (BootstrapDimensions.A_id p), X u id} :=
        measureReal_mono hsubset
    _ ≤ Real.exp (-((BootstrapDimensions.A_id p : ℝ) / 6) ^ 2 /
          (2 * (∑ _u : Fin (BootstrapDimensions.A_id p), c))) := htail
    _ = Real.exp (-(BootstrapDimensions.A_id p : ℝ) / 18) := by rw [hexponent]

/-- On the construction branch, the complement of literal column balance has
probability at most `1 / N`. Source: property (i) in
`sources/zip4/manuscript/appendix_b_communication.tex:195-207`; bit sampling and
branch dimensions in `sources/zip4/manuscript/07_public_setup.tex:5-25`. The
only branch inputs are the universal constant and the source inequality
`T > C_b m K b_N^2`. -/
theorem columnBalanced_compl_measure_le (C_b : ℝ) (p : ConstructorDimensions.Parameters)
    (hCb : 16 ≤ C_b) (hbranch : constructionBranchBound C_b p) :
    (idArrayMeasure p).real {id | ¬ columnBalanced p id} ≤
      (1 : ℝ) / (ConstructorDimensions.N p : ℝ) := by
  have hdim := construction_branch_dimensions C_b p hCb hbranch
  have hNpos : 0 < (ConstructorDimensions.N p : ℝ) :=
    Nat.cast_pos.mpr (ConstructorDimensions.N_pos p)
  have hApos : 0 < (BootstrapDimensions.A_id p : ℝ) :=
    Nat.cast_pos.mpr (BootstrapDimensions.A_id_pos p)
  have hA_ge_T : (p.T : ℝ) ≤ (BootstrapDimensions.A_id p : ℝ) := by
    exact_mod_cast hdim.2.1
  have hT_ge_log :
      36 * Real.log (ConstructorDimensions.N p : ℝ) ≤ (p.T : ℝ) := hdim.1
  have h2T_le_N :
      2 * (p.T : ℝ) ≤ (ConstructorDimensions.N p : ℝ) := by
    exact_mod_cast hdim.2.2
  have htailA :
      Real.exp (-(BootstrapDimensions.A_id p : ℝ) / 18) ≤
        Real.exp (-(p.T : ℝ) / 18) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have htailN_eq :
      Real.exp (-2 * Real.log (ConstructorDimensions.N p : ℝ)) =
        (ConstructorDimensions.N p : ℝ)⁻¹ ^ 2 := by
    rw [show -2 * Real.log (ConstructorDimensions.N p : ℝ) =
      -Real.log (ConstructorDimensions.N p : ℝ) +
        -Real.log (ConstructorDimensions.N p : ℝ) by ring,
      Real.exp_add, Real.exp_neg, Real.exp_log hNpos]
    ring
  have htailN :
      Real.exp (-(p.T : ℝ) / 18) ≤ (ConstructorDimensions.N p : ℝ)⁻¹ ^ 2 := by
    have hNlog :
        -(p.T : ℝ) / 18 ≤ -2 * Real.log (ConstructorDimensions.N p : ℝ) := by
      nlinarith [hT_ge_log]
    calc
      Real.exp (-(p.T : ℝ) / 18) ≤
          Real.exp (-2 * Real.log (ConstructorDimensions.N p : ℝ)) :=
        Real.exp_le_exp.mpr hNlog
      _ = (ConstructorDimensions.N p : ℝ)⁻¹ ^ 2 := htailN_eq
  have hsumExp :
      (∑ q : Fin p.T × Bool,
        Real.exp (-(BootstrapDimensions.A_id p : ℝ) / 18)) =
        (2 * (p.T : ℝ)) * Real.exp (-(BootstrapDimensions.A_id p : ℝ) / 18) := by
    simp [Finset.sum_const, Finset.card_univ]
    ring
  have hcomplement_subset :
      {id | ¬ columnBalanced p id} ⊆
        ⋃ q : Fin p.T × Bool,
          {id | ((Finset.univ.filter
            (fun u : Fin (BootstrapDimensions.A_id p) => id u q.1 = q.2)).card : ℝ) <
              (BootstrapDimensions.A_id p : ℝ) / 3} := by
    intro id hid
    simp only [Set.mem_ofPred_eq, columnBalanced, not_forall, not_le] at hid
    rcases hid with ⟨t, e, hfail⟩
    exact Set.mem_iUnion.mpr ⟨(t, e), hfail⟩
  calc
    (idArrayMeasure p).real {id | ¬ columnBalanced p id} ≤
        (idArrayMeasure p).real
          (⋃ q : Fin p.T × Bool,
            {id | ((Finset.univ.filter
              (fun u : Fin (BootstrapDimensions.A_id p) => id u q.1 = q.2)).card : ℝ) <
                (BootstrapDimensions.A_id p : ℝ) / 3}) :=
      measureReal_mono hcomplement_subset
    _ ≤ ∑ q : Fin p.T × Bool,
        (idArrayMeasure p).real
          {id | ((Finset.univ.filter
            (fun u : Fin (BootstrapDimensions.A_id p) => id u q.1 = q.2)).card : ℝ) <
              (BootstrapDimensions.A_id p : ℝ) / 3} :=
      measureReal_iUnion_fintype_le (μ := idArrayMeasure p) _
    _ ≤ ∑ q : Fin p.T × Bool,
        Real.exp (-(BootstrapDimensions.A_id p : ℝ) / 18) := by
      apply Finset.sum_le_sum
      intro q hq
      exact idArray_column_failure_measure_le p q.1 q.2
    _ = (2 * (p.T : ℝ)) * Real.exp (-(BootstrapDimensions.A_id p : ℝ) / 18) := hsumExp
    _ ≤ (ConstructorDimensions.N p : ℝ) *
        (ConstructorDimensions.N p : ℝ)⁻¹ ^ 2 := by
      calc
        (2 * (p.T : ℝ)) * Real.exp (-(BootstrapDimensions.A_id p : ℝ) / 18) ≤
            (2 * (p.T : ℝ)) * Real.exp (-(p.T : ℝ) / 18) :=
          mul_le_mul_of_nonneg_left htailA (by positivity)
        _ ≤ (2 * (p.T : ℝ)) * (ConstructorDimensions.N p : ℝ)⁻¹ ^ 2 :=
          mul_le_mul_of_nonneg_left htailN (by positivity)
        _ ≤ (ConstructorDimensions.N p : ℝ) *
            (ConstructorDimensions.N p : ℝ)⁻¹ ^ 2 :=
          mul_le_mul_of_nonneg_right h2T_le_N (sq_nonneg _)
    _ = (1 : ℝ) / (ConstructorDimensions.N p : ℝ) := by
      field_simp [hNpos.ne']

end Bandits.Support.IdentificationColumnBalance

end
