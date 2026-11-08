/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.CompletePublicTable

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Identification-array rectangle exclusion

Property (ii) of the identification-array event and its failure-mass bound.
Source: `sources/zip4/manuscript/appendix_b_communication.tex:195-213`.
-/

public section

open MeasureTheory Measure ProbabilityTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.CompletePublicTable
open scoped ENNReal

namespace Bandits.Support.IdentificationRectangleExclusion

/-- The source property (ii): every set of `6 * b_N` calendar times has fewer
than `L0` rows whose identification bits are all one on those times.
Source: `appendix_b_communication.tex:199`.
-/
@[expose] def idArrayPropertyII (p : ConstructorDimensions.Parameters)
    (x : CompletePublicTable.IDArray p) : Prop :=
  ∀ S : Finset (Fin p.T), S.card = 6 * b_N p →
    (Finset.univ.filter fun u : Fin (BootstrapDimensions.A_id p) =>
      ∀ t ∈ S, x u t = true).card < BootstrapDimensions.L0 p

/-- The all-one event on a finite row-by-time rectangle of the ID array. -/
@[expose] def allOneIDRectangle (p : ConstructorDimensions.Parameters)
    (R : Finset (Fin (BootstrapDimensions.A_id p))) (S : Finset (Fin p.T)) :
    Set (CompletePublicTable.IDArray p) :=
  {x | ∀ u ∈ R, ∀ t ∈ S, x u t = true}

private theorem fairBitLaw_true_ennreal : fairBitLaw {true} = (1 / 2 : ℝ≥0∞) := by
  norm_num [fairBitLaw, fairBitParameter, ProbabilityTheory.bernoulliMeasure_apply,
    unitInterval.toNNReal]
  rw [← ENNReal.coe_inv_two]
  have hNN : (⟨(1 / 2 : ℝ), by norm_num⟩ : NNReal) = (2⁻¹ : NNReal) := by
    ext
    norm_num
  exact congrArg ENNReal.ofNNReal hNN

/-- A fixed rectangle has the product probability of its independent fair ID
coordinates. This is derived from the actual nested product law
`CompletePublicTable.idArrayMeasure` using finite cylinder probabilities.
-/
theorem idArrayMeasure_allOneIDRectangle_real (p : ConstructorDimensions.Parameters)
    (R : Finset (Fin (BootstrapDimensions.A_id p))) (S : Finset (Fin p.T)) :
    (CompletePublicTable.idArrayMeasure p).real (allOneIDRectangle p R S) =
      (1 / 2 : ℝ) ^ (R.card * S.card) := by
  classical
  let rowEvent : Set (Fin p.T → Bool) := {y | ∀ t ∈ S, y t = true}
  have hrowEvent : rowEvent = (S : Set (Fin p.T)).pi (fun _ => ({true} : Set Bool)) := by
    ext y
    simp [rowEvent]
  have hrowMeasure :
      (Measure.pi (fun _ : Fin p.T => fairBitLaw)) rowEvent =
        (1 / 2 : ℝ≥0∞) ^ S.card := by
    rw [hrowEvent, Measure.pi_pi_finset]
    simp only [fairBitLaw_true_ennreal, Finset.prod_const]
  have hrectangleEvent :
      allOneIDRectangle p R S = (R : Set (Fin (BootstrapDimensions.A_id p))).pi
        (fun _ => rowEvent) := by
    ext x
    simp [allOneIDRectangle, rowEvent]
  have hrectangleMass :
      (CompletePublicTable.idArrayMeasure p) (allOneIDRectangle p R S) =
        (1 / 2 : ℝ≥0∞) ^ (R.card * S.card) := by
    rw [CompletePublicTable.idArrayMeasure, hrectangleEvent, Measure.pi_pi_finset]
    simp only [hrowMeasure, Finset.prod_const]
    calc
      ((1 / 2 : ℝ≥0∞) ^ S.card) ^ R.card =
          (1 / 2 : ℝ≥0∞) ^ (S.card * R.card) := by rw [← pow_mul]
      _ = (1 / 2 : ℝ≥0∞) ^ (R.card * S.card) := by rw [Nat.mul_comm]
  change ENNReal.toReal
    ((CompletePublicTable.idArrayMeasure p) (allOneIDRectangle p R S)) = _
  rw [hrectangleMass]
  simp

/-- The source dimensions imply `A_id ≤ N^2`, `T ≤ N`, `b_N ≥ 5`, and
`log N ≤ b_N log 2`. These are derived here from the accepted parameter domain
and literal dimension definitions. -/
private theorem sourceDimensionBounds (p : ConstructorDimensions.Parameters) :
    BootstrapDimensions.A_id p ≤ N p ^ 2 ∧ p.T ≤ N p ∧
      5 ≤ b_N p ∧ Real.log (N p : ℝ) ≤ (b_N p : ℝ) * Real.log 2 := by
  have hKm : 1 ≤ p.K * p.m := by
    exact Nat.succ_le_of_lt (Nat.mul_pos (K_pos p) (m_pos p))
  have hcoef : 2 ≤ 2 * p.K * p.m := by
    calc
      2 = 2 * 1 := by omega
      _ ≤ 2 * (p.K * p.m) := Nat.mul_le_mul_left 2 hKm
      _ = 2 * p.K * p.m := by ring
  have hNfactor : 2 * (p.T + 1) ≤ N p := by
    change 2 * (p.T + 1) ≤ 2 * p.K * p.m * (p.T + 1)
    exact Nat.mul_le_mul_right (p.T + 1) hcoef
  have hTleN : p.T ≤ N p := by omega
  have hBcast : (B_boot p : ℝ) ≤ (p.T : ℝ) := by
    exact_mod_cast B_boot_le_T p
  have hbpos : 0 < (b_N p : ℝ) := by
    exact_mod_cast b_N_pos p
  have hbge : (1 : ℝ) ≤ (b_N p : ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt (b_N_pos p))
  have hTnonneg : (0 : ℝ) ≤ (p.T : ℝ) := Nat.cast_nonneg _
  have hrate :
      (p.T : ℝ) * ((B_boot p : ℝ) + (b_N p : ℝ)) / (b_N p : ℝ) ≤
        (p.T : ℝ) + (p.T : ℝ) ^ 2 := by
    rw [div_le_iff₀ hbpos]
    have hTB : (p.T : ℝ) * (B_boot p : ℝ) ≤ (p.T : ℝ) ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hBcast hTnonneg]
    have hT2b : (p.T : ℝ) ^ 2 ≤ (p.T : ℝ) ^ 2 * (b_N p : ℝ) := by
      nlinarith [sq_nonneg (p.T : ℝ)]
    calc
      (p.T : ℝ) * ((B_boot p : ℝ) + (b_N p : ℝ)) =
          (p.T : ℝ) * (B_boot p : ℝ) + (p.T : ℝ) * (b_N p : ℝ) := by ring
      _ ≤ (p.T : ℝ) ^ 2 + (p.T : ℝ) * (b_N p : ℝ) :=
        add_le_add hTB le_rfl
      _ ≤ (p.T : ℝ) ^ 2 * (b_N p : ℝ) + (p.T : ℝ) * (b_N p : ℝ) :=
        add_le_add hT2b le_rfl
      _ = ((p.T : ℝ) + (p.T : ℝ) ^ 2) * (b_N p : ℝ) := by ring
  have hAreal : (BootstrapDimensions.A_id p : ℝ) <
      (p.T : ℝ) ^ 2 + (p.T : ℝ) + 1 := by
    have hratepos :
        0 < (p.T : ℝ) * ((B_boot p : ℝ) + (b_N p : ℝ)) / (b_N p : ℝ) :=
      div_pos (mul_pos (Nat.cast_pos.mpr (T_pos p))
        (add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) hbpos)) hbpos
    have hceil := Nat.ceil_lt_add_one (le_of_lt hratepos)
    dsimp [BootstrapDimensions.A_id] at hceil ⊢
    calc
      (⌈(p.T : ℝ) * ((B_boot p : ℝ) + (b_N p : ℝ)) / (b_N p : ℝ)⌉₊ : ℝ) <
          (p.T : ℝ) * ((B_boot p : ℝ) + (b_N p : ℝ)) / (b_N p : ℝ) + 1 := hceil
      _ ≤ (p.T : ℝ) ^ 2 + (p.T : ℝ) + 1 := by linarith [hrate]
  have hAnat : BootstrapDimensions.A_id p ≤ p.T ^ 2 + p.T := by
    have hAcast : BootstrapDimensions.A_id p < p.T ^ 2 + p.T + 1 := by
      exact_mod_cast hAreal
    omega
  have hNfactorR : 2 * ((p.T : ℝ) + 1) ≤ (N p : ℝ) := by
    exact_mod_cast hNfactor
  have hT2leN2 : (p.T : ℝ) ^ 2 + (p.T : ℝ) ≤ (N p : ℝ) ^ 2 := by
    nlinarith [sq_nonneg ((N p : ℝ) - 2 * ((p.T : ℝ) + 1))]
  have hA2 : BootstrapDimensions.A_id p ≤ N p ^ 2 := by
    exact hAnat.trans (by exact_mod_cast hT2leN2)
  have hb5 : 5 ≤ b_N p := by
    have h24 := BootstrapDimensions.twentyFour_le_N p
    have hpow : 2 ^ 4 < N p + 1 := by omega
    have hclog : 4 < Nat.clog 2 (N p + 1) :=
      (Nat.lt_clog_iff_pow_lt (by decide : 1 < 2)).2 hpow
    change 5 ≤ Nat.clog 2 (N p + 1)
    omega
  have hNpos : 0 < (N p : ℝ) := by
    exact_mod_cast N_pos p
  have hNpowNat : N p ≤ 2 ^ b_N p := by
    have hNlt : N p < 2 ^ b_N p := by
      simpa [D] using N_lt_D p
    exact hNlt.le
  have hNpow : (N p : ℝ) ≤ (2 : ℝ) ^ b_N p := by
    exact_mod_cast hNpowNat
  have hlogN : Real.log (N p : ℝ) ≤ (b_N p : ℝ) * Real.log 2 := by
    calc
      Real.log (N p : ℝ) ≤ Real.log ((2 : ℝ) ^ b_N p) :=
        Real.log_le_log hNpos hNpow
      _ = (b_N p : ℝ) * Real.log 2 := by rw [Real.log_pow]
  exact ⟨hA2, hTleN, hb5, hlogN⟩

/-- The mass of arrays failing property (ii) is at most `N⁻²` under the
existing complete-public-table ID-array law. The proof counts fixed-size
time and row sets, derives each rectangle probability from the product law,
and then applies the source logarithmic dimension estimates.
-/
theorem idArrayPropertyII_failure_mass_le (p : ConstructorDimensions.Parameters) :
    (CompletePublicTable.idArrayMeasure p).real
      {x | ¬ idArrayPropertyII p x} ≤ (1 / (N p : ℝ)) ^ 2 := by
  classical
  let q : ℕ := 6 * b_N p
  let L : ℕ := BootstrapDimensions.L0 p
  by_cases hq : q > p.T
  · have hgood : ∀ x : CompletePublicTable.IDArray p, idArrayPropertyII p x := by
      intro x S hS
      have hScard : S.card ≤ p.T := by
        calc
          S.card ≤ Fintype.card (Fin p.T) := Finset.card_le_univ S
          _ = p.T := Fintype.card_fin _
      omega
    have hbad : ({x : CompletePublicTable.IDArray p | ¬ idArrayPropertyII p x} :
        Set (CompletePublicTable.IDArray p)) = ∅ := by
      ext x
      simp [hgood x]
    rw [hbad]
    simp
  · by_cases hL : L > BootstrapDimensions.A_id p
    · have hgood : ∀ x : CompletePublicTable.IDArray p, idArrayPropertyII p x := by
        intro x S hS
        have hcount :
            (Finset.univ.filter fun u : Fin (BootstrapDimensions.A_id p) =>
              ∀ t ∈ S, x u t = true).card ≤ BootstrapDimensions.A_id p := by
          calc
            _ ≤ Fintype.card (Fin (BootstrapDimensions.A_id p)) := Finset.card_le_univ _
            _ = BootstrapDimensions.A_id p := Fintype.card_fin _
        change (Finset.univ.filter _).card < L
        omega
      have hbad : ({x : CompletePublicTable.IDArray p | ¬ idArrayPropertyII p x} :
          Set (CompletePublicTable.IDArray p)) = ∅ := by
        ext x
        simp [hgood x]
      rw [hbad]
      simp
    · have hqle : q ≤ p.T := Nat.le_of_not_gt hq
      have hLle : L ≤ BootstrapDimensions.A_id p := Nat.le_of_not_gt hL
      let timeChoices := (Finset.univ : Finset (Fin p.T)).powersetCard q
      let rowChoices :=
        (Finset.univ : Finset (Fin (BootstrapDimensions.A_id p))).powersetCard L
      let choices := timeChoices ×ˢ rowChoices
      have hbadSubset :
          ({x : CompletePublicTable.IDArray p | ¬ idArrayPropertyII p x} :
            Set (CompletePublicTable.IDArray p)) ⊆
            ⋃ c ∈ choices, allOneIDRectangle p c.2 c.1 := by
        intro x hx
        simp only [Set.mem_ofPred_eq, idArrayPropertyII] at hx
        push Not at hx
        rcases hx with ⟨S, hScard, hnotlt⟩
        let goodRows := Finset.univ.filter fun u : Fin (BootstrapDimensions.A_id p) =>
          ∀ t ∈ S, x u t = true
        have hrows : L ≤ goodRows.card := by omega
        obtain ⟨R, hRsub, hRcard⟩ := Finset.exists_subset_card_eq hrows
        have hScardq : S.card = q := by simpa [q] using hScard
        have hSchoice : S ∈ timeChoices := by
          simp [timeChoices, hScardq]
        have hRchoice : R ∈ rowChoices := by
          simp [rowChoices, hRcard]
        have hchoice : (S, R) ∈ choices := by
          simp [choices, hSchoice, hRchoice]
        have hrect : x ∈ allOneIDRectangle p R S := by
          intro u hu t ht
          exact (Finset.mem_filter.mp (hRsub hu)).2 t ht
        simp only [Set.mem_iUnion]
        exact ⟨(S, R), hchoice, hrect⟩
      have hsum :
          (∑ c ∈ choices,
              (CompletePublicTable.idArrayMeasure p).real
                (allOneIDRectangle p c.2 c.1)) =
            (Nat.choose (BootstrapDimensions.A_id p) L : ℝ) *
              (Nat.choose p.T q : ℝ) * (1 / 2 : ℝ) ^ (L * q) := by
        calc
          _ = ∑ c ∈ choices, (1 / 2 : ℝ) ^ (L * q) := by
            apply Finset.sum_congr rfl
            intro c hc
            have hcp := Finset.mem_product.mp hc
            have hScard' := (Finset.mem_powersetCard.mp hcp.1).2
            have hRcard' := (Finset.mem_powersetCard.mp hcp.2).2
            rw [idArrayMeasure_allOneIDRectangle_real, hRcard', hScard']
          _ = (choices.card : ℝ) * (1 / 2 : ℝ) ^ (L * q) := by simp
          _ = (Nat.choose (BootstrapDimensions.A_id p) L : ℝ) *
                (Nat.choose p.T q : ℝ) * (1 / 2 : ℝ) ^ (L * q) := by
            rw [Finset.card_product]
            simp [timeChoices, rowChoices]
            ring
      have hunion :
          (CompletePublicTable.idArrayMeasure p).real
            (⋃ c ∈ choices, allOneIDRectangle p c.2 c.1) ≤
              (Nat.choose (BootstrapDimensions.A_id p) L : ℝ) *
                (Nat.choose p.T q : ℝ) * (1 / 2 : ℝ) ^ (L * q) := by
        calc
          _ ≤ ∑ c ∈ choices,
                (CompletePublicTable.idArrayMeasure p).real
                  (allOneIDRectangle p c.2 c.1) :=
            measureReal_biUnion_finset_le choices _
          _ = _ := hsum
      have hfailure :
          (CompletePublicTable.idArrayMeasure p).real
            {x | ¬ idArrayPropertyII p x} ≤
              (Nat.choose (BootstrapDimensions.A_id p) L : ℝ) *
                (Nat.choose p.T q : ℝ) * (1 / 2 : ℝ) ^ (L * q) := by
        have hfinite :
            (CompletePublicTable.idArrayMeasure p)
              (⋃ c ∈ choices, allOneIDRectangle p c.2 c.1) ≠ ∞ := by
          have hle :
              (CompletePublicTable.idArrayMeasure p)
                (⋃ c ∈ choices, allOneIDRectangle p c.2 c.1) ≤ 1 := by
            calc
              _ ≤ (CompletePublicTable.idArrayMeasure p) Set.univ :=
                measure_mono (Set.subset_univ _)
              _ = 1 := measure_univ
          exact ne_of_lt (lt_of_le_of_lt hle ENNReal.one_lt_top)
        exact (measureReal_mono hbadSubset hfinite).trans hunion
      have hchooseA :
          (Nat.choose (BootstrapDimensions.A_id p) L : ℝ) ≤
            (BootstrapDimensions.A_id p : ℝ) ^ L := by
        exact_mod_cast Nat.choose_le_pow (BootstrapDimensions.A_id p) L
      have hchooseT : (Nat.choose p.T q : ℝ) ≤ (p.T : ℝ) ^ q := by
        exact_mod_cast Nat.choose_le_pow p.T q
      have hcounts :
          (Nat.choose (BootstrapDimensions.A_id p) L : ℝ) *
              (Nat.choose p.T q : ℝ) * (1 / 2 : ℝ) ^ (L * q) ≤
            (BootstrapDimensions.A_id p : ℝ) ^ L * (p.T : ℝ) ^ q /
              (2 : ℝ) ^ (L * q) := by
        calc
          _ ≤ (BootstrapDimensions.A_id p : ℝ) ^ L * (p.T : ℝ) ^ q *
                (1 / 2 : ℝ) ^ (L * q) := by
            gcongr
          _ = (BootstrapDimensions.A_id p : ℝ) ^ L * (p.T : ℝ) ^ q /
                (2 : ℝ) ^ (L * q) := by
            rw [one_div_pow]
            ring
      let P : ℝ := (BootstrapDimensions.A_id p : ℝ) ^ L * (p.T : ℝ) ^ q /
        (2 : ℝ) ^ (L * q)
      have hPpos : 0 < P := by
        dsimp [P]
        exact div_pos
          (mul_pos (pow_pos (by exact_mod_cast A_id_pos p) _)
            (pow_pos (by exact_mod_cast T_pos p) _))
          (pow_pos (by norm_num : (0 : ℝ) < 2) _)
      have hApos : 0 < (BootstrapDimensions.A_id p : ℝ) := by
        exact_mod_cast A_id_pos p
      have hTpos : 0 < (p.T : ℝ) := by
        exact_mod_cast T_pos p
      have hNpos : 0 < (N p : ℝ) := by
        exact_mod_cast N_pos p
      have ⟨hAdim, hTdim, hb5, hlogN⟩ := sourceDimensionBounds p
      have hlogA :
          Real.log (BootstrapDimensions.A_id p : ℝ) ≤ 2 * Real.log (N p : ℝ) := by
        calc
          Real.log (BootstrapDimensions.A_id p : ℝ) ≤
              Real.log ((N p : ℝ) ^ 2) :=
            Real.log_le_log hApos (by exact_mod_cast hAdim)
          _ = 2 * Real.log (N p : ℝ) := by rw [Real.log_pow]; norm_num
      have hlogT : Real.log (p.T : ℝ) ≤ Real.log (N p : ℝ) :=
        Real.log_le_log hTpos (by exact_mod_cast hTdim)
      have hqreal : (q : ℝ) = 6 * (b_N p : ℝ) := by
        simp [q]
      have hLreal : 2 * (b_N p : ℝ) ≤ (L : ℝ) := by
        dsimp [L]
        exact_mod_cast BootstrapDimensions.two_mul_b_N_le_L0 p
      have hlogP :
          Real.log P = (L : ℝ) * Real.log (BootstrapDimensions.A_id p : ℝ) +
            (q : ℝ) * Real.log (p.T : ℝ) -
              ((L * q : ℕ) : ℝ) * Real.log 2 := by
        dsimp [P]
        rw [Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity)
          (by positivity), Real.log_pow, Real.log_pow, Real.log_pow]
      have hLnonneg : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg _
      have hqnonneg : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg _
      have hlogPupper : Real.log P ≤ -2 * (b_N p : ℝ) ^ 2 * Real.log 2 := by
        calc
          Real.log P ≤ 2 * (L : ℝ) * Real.log (N p : ℝ) +
              (q : ℝ) * Real.log (N p : ℝ) -
                ((L * q : ℕ) : ℝ) * Real.log 2 := by
            rw [hlogP]
            have hfirst := mul_le_mul_of_nonneg_left hlogA hLnonneg
            have hsecond := mul_le_mul_of_nonneg_left hlogT hqnonneg
            nlinarith
          _ ≤ 2 * (L : ℝ) * ((b_N p : ℝ) * Real.log 2) +
              (q : ℝ) * ((b_N p : ℝ) * Real.log 2) -
                ((L * q : ℕ) : ℝ) * Real.log 2 := by
            exact sub_le_sub_right (add_le_add
              (mul_le_mul_of_nonneg_left hlogN
                (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hLnonneg))
              (mul_le_mul_of_nonneg_left hlogN hqnonneg)) _
          _ = (6 * (b_N p : ℝ) ^ 2 - 4 * (L : ℝ) * (b_N p : ℝ)) *
                Real.log 2 := by
            simp only [q, Nat.cast_mul]
            ring
          _ ≤ -2 * (b_N p : ℝ) ^ 2 * Real.log 2 := by
            apply mul_le_mul_of_nonneg_right _
              (le_of_lt (Real.log_pos (by norm_num : (1 : ℝ) < 2)))
            have hcoeff : 4 * (b_N p : ℝ) ^ 2 ≤
                2 * (L : ℝ) * (b_N p : ℝ) := by
              have hbnonneg : (0 : ℝ) ≤ (b_N p : ℝ) := Nat.cast_nonneg _
              have hfactor : (0 : ℝ) ≤ 2 * (b_N p : ℝ) :=
                mul_nonneg (by norm_num) hbnonneg
              have hmul := mul_le_mul_of_nonneg_right hLreal hfactor
              nlinarith
            nlinarith
      have hbge : (1 : ℝ) ≤ (b_N p : ℝ) := by
        exact_mod_cast (by omega : 1 ≤ b_N p)
      have hlogNnonneg : 0 ≤ Real.log (N p : ℝ) := by
        apply Real.log_nonneg
        exact_mod_cast (by omega : 1 ≤ N p)
      have hlogNle : Real.log (N p : ℝ) ≤ (b_N p : ℝ) ^ 2 * Real.log 2 := by
        calc
          Real.log (N p : ℝ) ≤ (b_N p : ℝ) * Real.log (N p : ℝ) := by
            nlinarith [mul_nonneg (sub_nonneg.mpr hbge) hlogNnonneg]
          _ ≤ (b_N p : ℝ) * ((b_N p : ℝ) * Real.log 2) :=
            mul_le_mul_of_nonneg_left hlogN (Nat.cast_nonneg _)
          _ = (b_N p : ℝ) ^ 2 * Real.log 2 := by ring
      have hrecipLog : Real.log (1 / (N p : ℝ) ^ 2) =
          -2 * Real.log (N p : ℝ) := by
        rw [Real.log_div (by norm_num) (by positivity), Real.log_one, Real.log_pow]
        simp
      have hlogCompare : -2 * (b_N p : ℝ) ^ 2 * Real.log 2 ≤
          Real.log (1 / (N p : ℝ) ^ 2) := by
        rw [hrecipLog]
        nlinarith
      have hPbound : P ≤ (1 / (N p : ℝ)) ^ 2 := by
        calc
          P = Real.exp (Real.log P) := (Real.exp_log hPpos).symm
          _ ≤ Real.exp (-2 * (b_N p : ℝ) ^ 2 * Real.log 2) :=
            Real.exp_le_exp.mpr hlogPupper
          _ ≤ Real.exp (Real.log (1 / (N p : ℝ) ^ 2)) :=
            Real.exp_le_exp.mpr hlogCompare
          _ = 1 / (N p : ℝ) ^ 2 :=
            Real.exp_log (div_pos (by norm_num : (0 : ℝ) < 1) (pow_pos hNpos 2))
          _ = (1 / (N p : ℝ)) ^ 2 := by rw [one_div_pow]
      exact hfailure.trans (hcounts.trans (by simpa [P] using hPbound))

end Bandits.Support.IdentificationRectangleExclusion
